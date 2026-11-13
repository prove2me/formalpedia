-- Prove2me | solution 1 for RepellingPairs.cost_inequality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:52:56.644104+00:00
-- url     : https://prove2.me/submissions/f5e9b00e-c85c-4dd9-90ac-7cf009ae6ec6

import Mathlib
import Theorems.Thm_RepellingPairs_cost_inequality_of_trivial_pair
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_IntegralFlow
import Theorems.Thm_RepellingPairs_claim_9_flow_dominance
import Theorems.Thm_RepellingPairs_lemma_10_dominance_implies_uncrossing
import Theorems.Thm_RepellingPairs_config_eq_of_dist_eq
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.CostIneq

open RepellingPairs


variable {k : ℕ}

/-- cost of a configuration for a symmetric `D` -/
def ccost (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (C : Config k) : ℝ :=
  (C.map (Sym2.lift ⟨D, hs⟩)).sum

theorem ccost_cons (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (x y : Fin k) (C : Config k) :
    ccost D hs (s(x, y) ::ₘ C) = D x y + ccost D hs C := by
  simp [ccost]

/-- Kalmanson for any cyclically ordered quadruple -/
theorem kal_cyc (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D) {p q r s : Fin k}
    (h : CyclicallyOrdered p q r s) :
    D p q + D r s ≤ D p r + D q s ∧ D p s + D q r ≤ D p r + D q s := by
  have hs := hD.symm
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have := hK p q r s h1 h2 h3
    simp only [max_le_iff] at this
    exact this
  · have := hK q r s p h1 h2 h3
    simp only [max_le_iff] at this
    rw [hs s p, hs q p, hs r p] at this
    constructor <;> linarith [this.1, this.2, hs r s, hs q r, hs p s, hs p q, hs p r]
  · have := hK r s p q h1 h2 h3
    simp only [max_le_iff] at this
    constructor <;> linarith [this.1, this.2, hs r s, hs q r, hs p s, hs p q, hs p r, hs r p,
      hs s q, hs q s, hs s p, hs q p, hs r q, hs s r]
  · have := hK s p q r h1 h2 h3
    simp only [max_le_iff] at this
    constructor <;> linarith [this.1, this.2, hs r s, hs q r, hs p s, hs p q, hs p r, hs r p,
      hs s q, hs q s, hs s p, hs q p, hs r q, hs s r]

theorem step_le (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D) {C C₁ : Config k}
    (h : Config.UncrossStep C C₁ ∨ Config.DegenerateStep C C₁) :
    ccost D hD.symm C₁ ≤ ccost D hD.symm C := by
  have hs := hD.symm
  rcases h with ⟨x, y, z, w, rest, hc, rfl, h1 | h1⟩ | ⟨x, y, w, rest, hxy, hxw, rfl, rfl⟩
  · subst h1
    simp only [ccost_cons]
    rcases hc with hc | hc
    · have := kal_cyc D hD hK hc
      linarith [this.1, hs z y, hs w y, hs w z, hs y w, hs z w]
    · have := kal_cyc D hD hK hc
      linarith [this.1, this.2, hs z y, hs w y, hs w z, hs y w, hs z w, hs y z]
  · subst h1
    simp only [ccost_cons]
    rcases hc with hc | hc
    · have := kal_cyc D hD hK hc
      linarith [this.1, this.2, hs z y, hs w y, hs w z, hs y w, hs z w, hs y z]
    · have := kal_cyc D hD hK hc
      linarith [this.1, this.2, hs z y, hs w y, hs w z, hs y w, hs z w, hs y z]
  · simp only [ccost_cons]
    have := hD.triangle y x w
    have h0 := hD.self x
    linarith [hs x y]

theorem reaches_le (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D) {C C' : Config k}
    (h : Config.Reaches C C') : ccost D hD.symm C' ≤ ccost D hD.symm C := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (step_le D hD hK hs).trans ih


theorem ccost_chords_F (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (F : DesignatedFlow k) :
    ccost D hs (DesignatedFlow.chords F) = DesignatedFlow.cost D F := by
  simp [ccost, DesignatedFlow.chords, DesignatedFlow.cost, Multiset.map_map, Function.comp_def]

theorem ccost_chords_F' {V : Type u} {E : Type v} {G : OSInstance V E k}
    (D : Fin k → Fin k → ℝ) (hs : ∀ i j, D i j = D j i) (F' : PathFlow G) :
    ccost D hs (PathFlow.chords F') = PathFlow.cost D F' := by
  simp [ccost, PathFlow.chords, PathFlow.cost, Multiset.map_map, Function.comp_def]

/-- the case of no trivial unit in `F` -/
theorem noTrivial_case {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F) (hF : NoTrivialPair F) :
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F := by
  have hdom := claim_9_flow_dominance G D hD hK P hgood F F' h2 h4 h5 hF
  rw [← ccost_chords_F D hD.symm, ← ccost_chords_F' D hD.symm]
  by_cases hstrict : ∃ i j, Config.dist (PathFlow.chords F') i j < Config.dist (DesignatedFlow.chords F) i j
  · have hloop : ∀ a, s(a, a) ∉ DesignatedFlow.chords F := by
      intro a ha
      simp only [DesignatedFlow.chords, Multiset.mem_map] at ha
      obtain ⟨p, hp, hpa⟩ := ha
      have h : p = (a, a) := by simpa using hpa
      exact hF p hp (by rw [h])
    have hr := lemma_10_dominance_implies_uncrossing (DesignatedFlow.chords F)
      (PathFlow.chords F') hloop h4 ⟨hdom, hstrict⟩
    exact reaches_le D hD hK hr
  · simp only [not_exists, not_lt] at hstrict
    have heq := config_eq_of_dist_eq (DesignatedFlow.chords F) (PathFlow.chords F') h4
      (fun i j => le_antisymm (hstrict i j) (hdom i j))
    rw [heq]


theorem mem_support_end {V : Type u} {E : Type v} {G : Multigraph V E} {a b : V} (p : G.Walk a b) :
    b ∈ p.support := by
  induction p with
  | nil v => simp [Multigraph.Walk.support]
  | cons e h p ih => simp [Multigraph.Walk.support, ih]

theorem edges_nil_of_loop {V : Type u} {E : Type v} {G : Multigraph V E} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (h : a = b) : p.edges = [] := by
  cases p with
  | nil v => rfl
  | cons e h' p' =>
    exfalso
    have h1 := mem_support_end p'
    have h2 : (Multigraph.Walk.cons e h' p').support.Nodup := hp
    simp only [Multigraph.Walk.support, List.nodup_cons] at h2
    exact h2.1 (h ▸ h1)

theorem load_trivial {V : Type u} {E : Type v} {G : OSInstance V E k} [DecidableEq E]
    (P : PathStructure G) (t : Fin k) (e : E) :
    (P.path t t).1.edges.count e = 0 := by
  rw [edges_nil_of_loop _ (P.path t t).2 rfl]; simp

theorem load_trivial' {V : Type u} {E : Type v} {G : OSInstance V E k} [DecidableEq E]
    (q : TerminalPath G) (h : q.src = q.tgt) (e : E) :
    q.path.1.edges.count e = 0 := by
  have := edges_nil_of_loop q.path.1 q.path.2 (by rw [h])
  rw [this]; simp

theorem main_ind {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) :
    ∀ (n : ℕ) (F : DesignatedFlow k) (F' : PathFlow G), Multiset.card F = n →
    Property2 P F F' → Property4 F F' → Property5 P F →
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F := by
  classical
  intro n
  induction n with
  | zero =>
    intro F F' hn h2 h4 h5
    exact noTrivial_case G D hD hK P hgood F F' h2 h4 h5
      (fun p hp => by simp [Multiset.card_eq_zero.mp hn] at hp)
  | succ n ih =>
    intro F F' hn h2 h4 h5
    by_cases hF : NoTrivialPair F
    · exact noTrivial_case G D hD hK P hgood F F' h2 h4 h5 hF
    · simp only [NoTrivialPair, not_forall, not_not] at hF
      obtain ⟨p, hp, hpt⟩ := hF
      obtain ⟨a, b⟩ := p
      simp only at hpt
      subst hpt
      by_cases hq : ∃ q ∈ F', q.src = a ∧ q.tgt = a
      · obtain ⟨q, hqm, hqs, hqt⟩ := hq
        have hFe : F = (a, a) ::ₘ F.erase (a, a) := (Multiset.cons_erase hp).symm
        have hFe' : F' = q ::ₘ F'.erase q := (Multiset.cons_erase hqm).symm
        have hcard : Multiset.card (F.erase (a, a)) = n := by
          rw [Multiset.card_erase_of_mem hp, hn]; rfl
        have hD0 : D a a = 0 := hD.self a
        have hdc : ∀ s : Sym2 (Fin k), s ∈ DesignatedFlow.chords (F.erase (a, a)) →
            s ∈ DesignatedFlow.chords F := by
          intro s hs
          simp only [DesignatedFlow.chords, Multiset.mem_map] at hs ⊢
          obtain ⟨x, hx, rfl⟩ := hs
          exact ⟨x, Multiset.mem_of_mem_erase hx, rfl⟩
        have hres := ih (F.erase (a, a)) (F'.erase q) hcard
          (by
            intro e
            have h := h2 e
            conv at h => rw [hFe, hFe']
            simp only [PathFlow.load, DesignatedFlow.load, Multiset.map_cons, Multiset.sum_cons,
              load_trivial P a e, load_trivial' q (hqs.trans hqt.symm) e] at h
            simpa [PathFlow.load, DesignatedFlow.load] using h)
          (by
            intro t
            have h := h4 t
            conv at h => rw [hFe, hFe']
            simp only [DesignatedFlow.chords, PathFlow.chords, Config.deg, Multiset.map_cons,
              Multiset.sum_cons, hqs, hqt] at h
            simpa [DesignatedFlow.chords, PathFlow.chords, Config.deg] using h)
          (fun s s' t' t hc h1 h2' => h5 s s' t' t hc (hdc _ h1) (hdc _ h2'))
        have c1 : DesignatedFlow.cost D F = DesignatedFlow.cost D (F.erase (a, a)) := by
          conv_lhs => rw [hFe]
          simp [DesignatedFlow.cost, hD0]
        have c2 : PathFlow.cost D F' = PathFlow.cost D (F'.erase q) := by
          conv_lhs => rw [hFe']
          simp [PathFlow.cost, hqs, hqt, hD0]
        rw [c1, c2]; exact hres
      · push Not at hq
        exact RepellingPairs.cost_inequality_of_trivial_pair G D hD hK P hgood F F' h2 h4 h5 a hp
          (fun q hqm ⟨h1, h2'⟩ => hq q hqm h1 h2')

end RepellingPairs.Dev.CostIneq

namespace RepellingPairs


theorem chk_cost_inequality {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F) :
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F :=
  Dev.CostIneq.main_ind G D hD hK P hgood _ F F' rfl h2 h4 h5

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_cost_inequality := @RepellingPairs.chk_cost_inequality
