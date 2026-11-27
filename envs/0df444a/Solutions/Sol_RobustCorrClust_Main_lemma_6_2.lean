-- Prove2me | solution 1 for RobustCorrClust.Main.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-27T01:30:43.670707+00:00
-- url     : https://prove2.me/submissions/7087c0da-7d8a-4201-8744-a6c3816eb915

import Mathlib
import Definitions.Def_RobustCorrClust_Main_SignedGraph

open RobustCorrClust RobustCorrClust.Main
open Sym2 Classical
open CorrClustBBC.Cautious

/-! Lemma 6.2 (p. 44), both parts: (i) `cost_G(C) ≤ cost_Q(C) + |E⁺_G △ E⁺_Q|` for every
clustering `C`; (ii) if a randomized algorithm on `Q` returns a clustering distributed as `μ`
(a probability distribution on labelings `ℓ : Fin n → Fin n`, clustering = equal labels) with
`E_μ[cost_Q] ≤ β OPT(Q)`, and `C*` is an optimal clustering of `G`, then
`E_μ[cost_G] ≤ β cost_Q(C*) + |E⁺_G △ E⁺_Q|`. -/

namespace P2MHole01_04d3a10f
theorem solution {n : ℕ} (G Q : SimpleGraph (Fin n)) (r : Fin n → Fin n → Prop) (u v : Fin n) :
  IsMistake G r u v → IsMistake Q r u v ∨ s(u, v) ∈ symmDiff G.edgeFinset Q.edgeFinset := by
  intro hm
  rcases hm with ⟨hne, hcase⟩
  cases hcase with
  | inl hgp =>
    by_cases hq : Q.Adj u v
    · left
      exact ⟨hne, Or.inl ⟨hq, hgp.2⟩⟩
    · right
      rw [Finset.mem_symmDiff]
      exact Or.inl ⟨by simp [hgp.1], by simp [hq]⟩
  | inr hgn =>
    by_cases hq : Q.Adj u v
    · right
      rw [Finset.mem_symmDiff]
      exact Or.inr ⟨by simp [hq], by simp [hgn.1]⟩
    · left
      exact ⟨hne, Or.inr ⟨hq, hgn.2⟩⟩
end P2MHole01_04d3a10f

-- riskiest
/-- Per unordered pair: a mistake `{u, v}` of `G` w.r.t. the relation `r` is either a
mistake of `Q` w.r.t. `r`, or the edge `{u, v}` is positive in exactly one of the two
graphs, i.e. it lies in the symmetric difference of the positive edge sets. -/
lemma mistake_transfer {n : ℕ} (G Q : SimpleGraph (Fin n)) (r : Fin n → Fin n → Prop)
    (u v : Fin n) :
    IsMistake G r u v →
    IsMistake Q r u v ∨ Sym2.mk u v ∈ symmDiff (G.edgeFinset) (Q.edgeFinset) := by
  (first | exact P2MHole01_04d3a10f.solution G Q r u v | (apply P2MHole01_04d3a10f.solution <;> assumption))

namespace P2MHole02_5303fb34
universe u_1
theorem solution {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {p q : α → Prop}
  (s : Finset α) (h : ∀ (x : α), p x → q x ∨ x ∈ s) :
  (Finset.filter p Finset.univ).card ≤ (Finset.filter q Finset.univ).card + s.card := by
  have hsub : Finset.filter p Finset.univ ⊆ Finset.filter q Finset.univ ∪ s := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union]
    rcases h x hx.2 with hq | hs
    · left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hq⟩
    · right
      exact hs
  calc
    (Finset.filter p Finset.univ).card ≤ (Finset.filter q Finset.univ ∪ s).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.filter q Finset.univ).card + s.card :=
      Finset.card_union_le _ _
end P2MHole02_5303fb34

/-- General counting: if every element satisfying `p` satisfies `q` or lies in the
Finset `s`, then the number of `p`-elements is at most the number of `q`-elements
plus the size of `s`. -/
lemma filter_card_le {α : Type*} [Fintype α] [DecidableEq α] {p q : α → Prop} (s : Finset α)
    (h : ∀ x, p x → q x ∨ x ∈ s) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card + s.card := by
  (first | exact P2MHole02_5303fb34.solution s h | (apply P2MHole02_5303fb34.solution <;> assumption))

namespace P2MHole03_4092f662
theorem solution {n : ℕ} (H : SimpleGraph (Fin n)) (D : Setoid (Fin n)) : OPT H ≤ cost H D := by
  have hm : cost H D ∈ Set.range (cost H) := ⟨D, rfl⟩
  have hne : ∃ n, n ∈ Set.range (cost H) := ⟨cost H D, hm⟩
  let d : Decidable (∃ n, n ∈ Set.range (cost H)) := Classical.dec _
  dsimp only [OPT, sInf]
  have heq : (if d : ∃ n, n ∈ Set.range (cost H) then Nat.find hne else 0) = Nat.find hne := by
    exact if_pos hne
  have hle : Nat.find hne ≤ cost H D := Nat.find_le hm
  exact heq ▸ hle
end P2MHole03_4092f662

/-- `OPT H` is the least cost over all clusterings, so in particular
`OPT H ≤ cost H D` for every clustering `D` of `H`. -/
lemma OPT_le_cost {n : ℕ} (H : SimpleGraph (Fin n)) (D : Setoid (Fin n)) :
    OPT H ≤ cost H D := by
  (first | exact P2MHole03_4092f662.solution H D | (apply P2MHole03_4092f662.solution <;> assumption))

namespace P2MHole04_09f3833b
/-- The set of symmetric pairs `{u, v}` (u ≠ v) that are mistakes of the relation `r` in `H`. -/
noncomputable def mistakeSet {n : ℕ} (H : SimpleGraph (Fin n)) (r : Fin n → Fin n → Prop) :
    Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Sym2 (Fin n))).filter (fun e => ∃ u v, e = s(u, v) ∧ IsMistake H r u v)

lemma cost_eq_mistakeSet {n : ℕ} (H : SimpleGraph (Fin n)) (D : Setoid (Fin n)) :
    cost H D = (mistakeSet H D.r).card := by
  dsimp [cost, mistakes, mistakeSet]
  congr 1
  ext e
  simp

lemma in_edge {n : ℕ} (H : SimpleGraph (Fin n)) (u v : Fin n) (_hne : u ≠ v) (hadj : H.Adj u v) :
    s(u, v) ∈ H.edgeFinset := by
  simp [SimpleGraph.mem_edgeFinset]
  tauto

lemma not_in_edge {n : ℕ} (H : SimpleGraph (Fin n)) (u v : Fin n) (hnot : ¬ H.Adj u v) :
    s(u, v) ∉ H.edgeFinset := by
  simp [SimpleGraph.mem_edgeFinset]
  tauto

/-- Every mistake pair of `G` (w.r.t. `D.r`) is either a mistake pair of `Q`, or a pair whose
    adjacency differs between `G` and `Q`. -/
lemma mistakeSet_subset {n : ℕ} (G Q : SimpleGraph (Fin n)) (D : Setoid (Fin n)) :
    mistakeSet G D.r ⊆ mistakeSet Q D.r ∪ symmDiff G.edgeFinset Q.edgeFinset := by
  intro e he
  simp [mistakeSet, Finset.mem_filter, Finset.mem_univ] at he
  obtain ⟨u, v, hEq, hm⟩ := he
  dsimp only [IsMistake] at hm
  obtain ⟨hne, hcase⟩ := hm
  by_cases hQ : Q.Adj u v
  · by_cases hD : D.r u v
    · -- Q.Adj ∧ D.r: then ¬G.Adj, so e is in Q.edgeFinset \ G.edgeFinset
      have hnotG : ¬ G.Adj u v := by tauto
      have hSD : e ∈ symmDiff G.edgeFinset Q.edgeFinset := by
        rw [Finset.mem_symmDiff]
        exact Or.inr ⟨by rw [hEq]; exact in_edge Q u v hne hQ,
                      by rw [hEq]; exact not_in_edge G u v hnotG⟩
      simp only [Finset.mem_union]
      exact Or.inr hSD
    · -- Q.Adj ∧ ¬D.r: e is a Q-mistake (Q.Adj ∧ ¬D.r)
      have hQM : IsMistake Q D.r u v := ⟨hne, Or.inl ⟨hQ, by tauto⟩⟩
      have hMQ : e ∈ mistakeSet Q D.r := by
        simp [mistakeSet, Finset.mem_filter, Finset.mem_univ]
        exact ⟨u, v, hEq, hQM⟩
      simp only [Finset.mem_union]
      exact Or.inl hMQ
  · by_cases hD : D.r u v
    · -- ¬Q.Adj ∧ D.r: e is a Q-mistake (¬Q.Adj ∧ D.r)
      have hQM : IsMistake Q D.r u v := ⟨hne, Or.inr ⟨by tauto, hD⟩⟩
      have hMQ : e ∈ mistakeSet Q D.r := by
        simp [mistakeSet, Finset.mem_filter, Finset.mem_univ]
        exact ⟨u, v, hEq, hQM⟩
      simp only [Finset.mem_union]
      exact Or.inl hMQ
    · -- ¬Q.Adj ∧ ¬D.r: then G.Adj, so e is in G.edgeFinset \ Q.edgeFinset
      have hG : G.Adj u v := by tauto
      have hSD : e ∈ symmDiff G.edgeFinset Q.edgeFinset := by
        rw [Finset.mem_symmDiff]
        exact Or.inl ⟨by rw [hEq]; exact in_edge G u v hne hG,
                      by rw [hEq]; exact not_in_edge Q u v hQ⟩
      simp only [Finset.mem_union]
      exact Or.inr hSD

theorem solution : ∀ {n : ℕ} (G Q : SimpleGraph (Fin n)) (D : Setoid (Fin n)),
  cost G D ≤ cost Q D + symmDiffCount G Q := by
  intro n G Q D
  calc (cost G D : ℕ) = (mistakeSet G D.r).card := cost_eq_mistakeSet G D
    _ ≤ ((mistakeSet Q D.r) ∪ (symmDiff G.edgeFinset Q.edgeFinset)).card :=
        Finset.card_mono (mistakeSet_subset G Q D)
    _ ≤ (mistakeSet Q D.r).card + (symmDiff G.edgeFinset Q.edgeFinset).card :=
        Finset.card_union_le _ _
    _ = cost Q D + symmDiffCount G Q := by
        rw [← cost_eq_mistakeSet, ← symmDiffCount]
end P2MHole04_09f3833b

/-- Lemma 6.2 (p. 44), both parts: (i) `cost_G(C) ≤ cost_Q(C) + |E⁺_G △ E⁺_Q|` for every
clustering `C`; (ii) if a randomized algorithm on `Q` returns a clustering distributed as `μ`
(a probability distribution on labelings `ℓ : Fin n → Fin n`, clustering = equal labels) with
`E_μ[cost_Q] ≤ β OPT(Q)`, and `C*` is an optimal clustering of `G`, then
`E_μ[cost_G] ≤ β cost_Q(C*) + |E⁺_G △ E⁺_Q|`. -/
theorem solution {n : ℕ} (G Q : SimpleGraph (Fin n)) :
    (∀ D : Setoid (Fin n), cost G D ≤ cost Q D + symmDiffCount G Q) ∧
    ∀ (β : ℝ) (μ : (Fin n → Fin n) → ℝ) (Cstar : Setoid (Fin n)),
      0 ≤ β → IsOptimal G Cstar → (∀ ℓ, 0 ≤ μ ℓ) → ∑ ℓ, μ ℓ = 1 →
      ∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ) ≤ β * (OPT Q : ℝ) →
      ∑ ℓ, μ ℓ * (cost G (Setoid.ker ℓ) : ℝ) ≤
        β * (cost Q Cstar : ℝ) + (symmDiffCount G Q : ℝ) := by
  -- part (i)
  have hi : ∀ D : Setoid (Fin n), cost G D ≤ cost Q D + symmDiffCount G Q := (by first | (apply P2MHole04_09f3833b.solution <;> assumption))
  refine ⟨hi, ?_⟩
  -- part (ii)
  intro β μ Cstar hβ hopt hμn hμ1 happrox
  have hpt (ℓ : Fin n → Fin n) :
      (cost G (Setoid.ker ℓ) : ℝ) ≤ (cost Q (Setoid.ker ℓ) : ℝ) + (symmDiffCount G Q : ℝ) := by
    exact_mod_cast hi (Setoid.ker ℓ)
  have hsum1 : ∑ ℓ, μ ℓ * (cost G (Setoid.ker ℓ) : ℝ) ≤
        ∑ ℓ, μ ℓ * ((cost Q (Setoid.ker ℓ) : ℝ) + (symmDiffCount G Q : ℝ)) := by
    apply Finset.sum_le_sum
    intro ℓ _
    exact mul_le_mul_of_nonneg_left (hpt ℓ) (hμn ℓ)
  have hsum2 : ∑ ℓ, μ ℓ * ((cost Q (Setoid.ker ℓ) : ℝ) + (symmDiffCount G Q : ℝ)) =
        (∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ)) + (symmDiffCount G Q : ℝ) := by
    calc
      _ = ∑ ℓ, (μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ) + μ ℓ * (symmDiffCount G Q : ℝ)) := by
        simp only [mul_add]
      _ = (∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ)) + ∑ ℓ, μ ℓ * (symmDiffCount G Q : ℝ) :=
        Finset.sum_add_distrib
      _ = (∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ)) + (∑ ℓ, μ ℓ) * (symmDiffCount G Q : ℝ) := by
        rw [← Finset.sum_mul]
      _ = (∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ)) + (symmDiffCount G Q : ℝ) := by
        rw [hμ1, one_mul]
  have hoPT : (OPT Q : ℝ) ≤ (cost Q Cstar : ℝ) := Nat.cast_le.mpr (OPT_le_cost Q Cstar)
  have hβopt : β * (OPT Q : ℝ) ≤ β * (cost Q Cstar : ℝ) := mul_le_mul_of_nonneg_left hoPT hβ
  calc
    ∑ ℓ, μ ℓ * (cost G (Setoid.ker ℓ) : ℝ) ≤
        ∑ ℓ, μ ℓ * ((cost Q (Setoid.ker ℓ) : ℝ) + (symmDiffCount G Q : ℝ)) := hsum1
    _ = (∑ ℓ, μ ℓ * (cost Q (Setoid.ker ℓ) : ℝ)) + (symmDiffCount G Q : ℝ) := hsum2
    _ ≤ β * (OPT Q : ℝ) + (symmDiffCount G Q : ℝ) := by linarith [happrox]
    _ ≤ β * (cost Q Cstar : ℝ) + (symmDiffCount G Q : ℝ) := by linarith [hβopt]
