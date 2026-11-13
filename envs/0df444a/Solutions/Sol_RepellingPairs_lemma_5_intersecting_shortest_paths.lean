-- Prove2me | solution 1 for RepellingPairs.lemma_5_intersecting_shortest_paths
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:17:39.914729+00:00
-- url     : https://prove2.me/submissions/15ae18ce-d2f2-4642-8a4e-b18dd36bb67e

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_PathLength
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Lemma5

open scoped ENNReal


variable {V : Type u} {E : Type v} {G : RepellingPairs.Multigraph V E}

open RepellingPairs.Multigraph

theorem edges_append {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil v => simp [Walk.append, Walk.edges]
  | cons e h p ih => simp [Walk.append, Walk.edges, ih]

theorem edges_reverse {u w : V} (p : G.Walk u w) : p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil v => simp [Walk.reverse, Walk.edges]
  | cons e h p ih => simp [Walk.reverse, Walk.edges, edges_append, ih]

theorem len_append (ℓ : E → ℝ) {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    (p.append q).len ℓ = p.len ℓ + q.len ℓ := by
  simp [Walk.len, edges_append]

theorem len_reverse (ℓ : E → ℝ) {u w : V} (p : G.Walk u w) : p.reverse.len ℓ = p.len ℓ := by
  simp [Walk.len, edges_reverse, List.map_reverse, List.sum_reverse]

theorem len_nonneg (ℓ : E → ℝ) (hℓ : ∀ e, 0 ≤ ℓ e) {u w : V} (p : G.Walk u w) : 0 ≤ p.len ℓ := by
  unfold Walk.len
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact hℓ e

/-- suffix from a vertex of the walk -/
theorem exists_suffix {v w : V} (q : G.Walk v w) (x : V) (hx : x ∈ q.support) :
    ∃ r : G.Walk x w, r.support.Sublist q.support ∧ r.edges.Sublist q.edges := by
  induction q with
  | nil v =>
    simp [Walk.support] at hx
    subst hx
    exact ⟨Walk.nil _, List.Sublist.refl _, List.Sublist.refl _⟩
  | cons e h q ih =>
    rename_i u v' w'
    simp only [Walk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨Walk.cons e h q, List.Sublist.refl _, List.Sublist.refl _⟩
    · obtain ⟨r, h1, h2⟩ := ih hx
      exact ⟨r, h1.cons _, h2.cons _⟩

theorem exists_path {u w : V} (p : G.Walk u w) :
    ∃ q : G.Walk u w, q.IsPath ∧ q.edges.Sublist p.edges := by
  induction p with
  | nil v => exact ⟨Walk.nil v, by simp [Walk.IsPath, Walk.support], List.Sublist.refl _⟩
  | cons e h p ih =>
    rename_i u v' w'
    obtain ⟨q, hq, hs⟩ := ih
    by_cases hu : u ∈ q.support
    · obtain ⟨r, h1, h2⟩ := exists_suffix q u hu
      exact ⟨r, hq.sublist h1, (h2.trans hs).cons _⟩
    · refine ⟨Walk.cons e h q, ?_, hs.cons_cons _⟩
      simp only [Walk.IsPath, Walk.support, List.nodup_cons]
      exact ⟨hu, hq⟩

theorem dist_le_walk (ℓ : E → ℝ) (hℓ : ∀ e, 0 ≤ ℓ e) {u w : V} (p : G.Walk u w) :
    G.distG ℓ u w ≤ ENNReal.ofReal (p.len ℓ) := by
  obtain ⟨q, hq, hs⟩ := exists_path p
  have hle : q.len ℓ ≤ p.len ℓ := by
    unfold Walk.len
    apply List.Sublist.sum_le_sum (hs.map ℓ)
    · intro x hx
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
      exact hℓ e
  calc G.distG ℓ u w ≤ ENNReal.ofReal ((⟨q, hq⟩ : G.Path u w).1.len ℓ) :=
        iInf_le (fun p : G.Path u w => ENNReal.ofReal (p.1.len ℓ)) ⟨q, hq⟩
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

theorem exists_split {a b : V} (p : G.Walk a b) (x : V) (hx : x ∈ p.support) :
    ∃ (p₁ : G.Walk a x) (p₂ : G.Walk x b), p₁.edges ++ p₂.edges = p.edges := by
  induction p with
  | nil v =>
    simp [Walk.support] at hx
    subst hx
    exact ⟨Walk.nil _, Walk.nil _, by simp [Walk.edges]⟩
  | cons e h p ih =>
    rename_i u v' w'
    simp only [Walk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨Walk.nil _, Walk.cons e h p, by simp [Walk.edges]⟩
    · obtain ⟨p₁, p₂, h1⟩ := ih hx
      exact ⟨Walk.cons e h p₁, p₂, by simp [Walk.edges, h1]⟩

theorem len_split (ℓ : E → ℝ) {a b x : V} (p : G.Walk a b) (p₁ : G.Walk a x) (p₂ : G.Walk x b)
    (h : p₁.edges ++ p₂.edges = p.edges) : p₁.len ℓ + p₂.len ℓ = p.len ℓ := by
  simp [Walk.len, ← h]

theorem dist_eq_of_shortest (ℓ : E → ℝ) (hℓ : ∀ e, 0 ≤ ℓ e) {a b : V} (P : G.Path a b)
    (hP : P.1.IsShortest ℓ) : G.distG ℓ a b = ENNReal.ofReal (P.1.len ℓ) := by
  apply le_antisymm (dist_le_walk ℓ hℓ P.1)
  apply le_iInf
  intro q
  exact ENNReal.ofReal_le_ofReal (hP q)

end RepellingPairs.Dev.Lemma5

namespace RepellingPairs


open RepellingPairs.Dev.Lemma5
open scoped ENNReal

theorem chk_lemma_5_intersecting_shortest_paths {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (ℓ : E → ℝ) (hℓ : ∀ e, 0 ≤ ℓ e) {a b c d : V}
    (P : G.Path a b) (Q : G.Path c d) (hP : P.1.IsShortest ℓ) (hQ : Q.1.IsShortest ℓ)
    (hint : ¬ P.1.VertexDisjoint Q.1) :
    G.distG ℓ a c + G.distG ℓ b d ≤ G.distG ℓ a b + G.distG ℓ c d ∧
      G.distG ℓ a d + G.distG ℓ b c ≤ G.distG ℓ a b + G.distG ℓ c d := by
  unfold Multigraph.Walk.VertexDisjoint at hint
  push Not at hint
  obtain ⟨x, hxP, hxQ⟩ := hint
  obtain ⟨p₁, p₂, h1⟩ := exists_split P.1 x hxP
  obtain ⟨q₁, q₂, h2⟩ := exists_split Q.1 x hxQ
  have e1 := len_split ℓ P.1 p₁ p₂ h1
  have e2 := len_split ℓ Q.1 q₁ q₂ h2
  have n1 := len_nonneg ℓ hℓ p₁
  have n2 := len_nonneg ℓ hℓ p₂
  have n3 := len_nonneg ℓ hℓ q₁
  have n4 := len_nonneg ℓ hℓ q₂
  rw [dist_eq_of_shortest ℓ hℓ P hP, dist_eq_of_shortest ℓ hℓ Q hQ, ← e1, ← e2]
  have A := dist_le_walk ℓ hℓ (p₁.append q₁.reverse)
  have B := dist_le_walk ℓ hℓ (p₂.reverse.append q₂)
  have C := dist_le_walk ℓ hℓ (p₁.append q₂)
  have D := dist_le_walk ℓ hℓ (p₂.reverse.append q₁.reverse)
  simp only [len_append, len_reverse] at A B C D
  constructor
  · refine (add_le_add A B).trans ?_
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · refine (add_le_add C D).trans ?_
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_lemma_5_intersecting_shortest_paths := @RepellingPairs.chk_lemma_5_intersecting_shortest_paths
