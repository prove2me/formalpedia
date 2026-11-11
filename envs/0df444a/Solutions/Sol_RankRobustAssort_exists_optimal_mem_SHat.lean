-- Prove2me | solution 1 for RankRobustAssort.exists_optimal_mem_SHat
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:57:23.437335+00:00
-- url     : https://prove2.me/submissions/ec086d3a-cb76-46a4-baf7-08f19f73ac93

import Definitions.Def_RankRobustAssort_IsTop
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Lean.Elab.Tactic.Omega
import Definitions.Def_RankRobustAssort_consistentSet
import Definitions.Def_RankRobustAssort_revenue
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Definitions.Def_RankRobustAssort_IsOptimalRO
import Definitions.Def_RankRobustAssort_SHat
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Choose

-- Component: P077Top
set_option autoImplicit false

open RankRobustAssort
open scoped BigOperators

namespace S02RankRobust

/-- Rankings assign distinct preference positions to the products. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin (n + 1))

/-- A nonempty assortment has at most one most preferred product. -/
theorem isTop_unique {n : ℕ} {σ : Ranking n} {S : Finset (Fin (n + 1))}
    {i j : Fin (n + 1)} (hi : IsTop σ S i) (hj : IsTop σ S j) : i = j := by
  exact σ.injective (le_antisymm (hi.2 j hj.1) (hj.2 i hi.1))

/-- Every nonempty assortment has a most preferred product. -/
theorem exists_isTop {n : ℕ} (σ : Ranking n) (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) : ∃ i, IsTop σ S i := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S σ hS
  exact ⟨i, hi, hmin⟩

/-- The revenue earned from an assortment under one deterministic ranking. -/
noncomputable def rankRevenue {n : ℕ} (r : Fin (n + 1) → ℝ) (σ : Ranking n)
    (S : Finset (Fin (n + 1))) : ℝ := by
  classical
  exact ∑ k, if IsTop σ S k then r k else 0

/-- A deterministic ranking earns the revenue of its unique winner. -/
theorem rankRevenue_of_top {n : ℕ} {r : Fin (n + 1) → ℝ} {σ : Ranking n}
    {S : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : IsTop σ S i) :
    rankRevenue r σ S = r i := by
  classical
  unfold rankRevenue
  rw [Finset.sum_eq_single i]
  · simp only [if_pos hi]
  · intro j _ hji
    have hj : ¬ IsTop σ S j := fun hj => hji (isTop_unique hj hi)
    simp only [if_neg hj]
  · intro hi'
    exact False.elim (hi' (Finset.mem_univ i))

end S02RankRobust

-- Component: P077Ranking
set_option autoImplicit false

namespace S02RankRobust

open RankRobustAssort

/-- Moving the last rank of an interval to its first position preserves the
relative order of all other ranks. -/
theorem cycleIcc_le_iff_of_ne_last {n : ℕ} (a b x y : Fin (n + 1))
    (hab : a ≤ b) (hx : x ≠ b) (hy : y ≠ b) :
    Fin.cycleIcc a b x ≤ Fin.cycleIcc a b y ↔ x ≤ y := by
  obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq hx
  obtain ⟨v, rfl⟩ := Fin.exists_succAbove_eq hy
  have hu := congrFun (Fin.cycleIcc_comp_succAbove a b hab) u
  have hv := congrFun (Fin.cycleIcc_comp_succAbove a b hab) v
  simp only [Function.comp_apply] at hu hv
  rw [hu, hv]
  simp only [Fin.succAbove_le_succAbove_iff]

/-- The strict version of stable rank insertion. -/
theorem cycleIcc_lt_iff_of_ne_last {n : ℕ} (a b x y : Fin (n + 1))
    (hab : a ≤ b) (hx : x ≠ b) (hy : y ≠ b) :
    Fin.cycleIcc a b x < Fin.cycleIcc a b y ↔ x < y := by
  obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq hx
  obtain ⟨v, rfl⟩ := Fin.exists_succAbove_eq hy
  have hu := congrFun (Fin.cycleIcc_comp_succAbove a b hab) u
  have hv := congrFun (Fin.cycleIcc_comp_succAbove a b hab) v
  simp only [Function.comp_apply] at hu hv
  rw [hu, hv]
  simp only [Fin.succAbove_lt_succAbove_iff]

/-- An added product that does not win leaves the original winner unchanged. -/
theorem isTop_insert_iff_of_not_top_insert {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (S : Finset (Fin (n + 1)))
    (i k : Fin (n + 1)) (hi : ¬ IsTop σ (insert i S) i) :
    IsTop σ S k ↔ IsTop σ (insert i S) k := by
  classical
  constructor
  · rintro ⟨hk, hmin⟩
    refine ⟨Finset.mem_insert_of_mem hk, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · by_contra hki
      apply hi
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · exact (le_of_lt (lt_of_not_ge hki)).trans (hmin j hj)
    · exact hmin j hj
  · intro hk
    refine ⟨?_, fun j hj => hk.2 j (Finset.mem_insert_of_mem hj)⟩
    rcases Finset.mem_insert.mp hk.1 with rfl | hkS
    · exact (hi hk).elim
    · exact hkS

/-- A ranking can be transferred from the enlarged assortment to the old one
while preserving every choice from a set whose inclusion of `i'` entails `i`.
When the inserted product wins, stably promote `i'` to just after it. -/
theorem ranking_transfer {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (i i' : Fin (n + 1))
    (hi : i ∉ S) (hi' : i' ∈ S) :
    ∃ τ : Equiv.Perm (Fin (n + 1)),
      (∀ T : Finset (Fin (n + 1)), (i' ∈ T → i ∈ T) →
        ∀ k, IsTop τ T k ↔ IsTop σ T k) ∧
      ((∀ k, IsTop τ S k ↔ IsTop σ (insert i S) k) ∨
        (IsTop τ S i' ∧ IsTop σ (insert i S) i)) := by
  classical
  by_cases htop : IsTop σ (insert i S) i
  · have hii' : i ≠ i' := by
      intro heq
      subst i'
      exact hi hi'
    have hσ : σ i < σ i' :=
      lt_of_le_of_ne (htop.2 i' (Finset.mem_insert_of_mem hi')) (σ.injective.ne hii')
    let a : Fin (n + 1) := ⟨(σ i).val + 1, by
      have hσnat : (σ i).val < (σ i').val := hσ
      exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hσnat) (σ i').isLt⟩
    have hab : a ≤ σ i' := by
      change (σ i).val + 1 ≤ (σ i').val
      exact Nat.succ_le_iff.mpr hσ
    have hai : σ i < a := by
      change (σ i).val < (σ i).val + 1
      exact Nat.lt_succ_self _
    let τ : Equiv.Perm (Fin (n + 1)) := σ.trans (Fin.cycleIcc a (σ i'))
    have hτi : τ i = σ i := by
      change Fin.cycleIcc a (σ i') (σ i) = σ i
      exact Fin.cycleIcc_of_lt hai
    have hτi' : τ i' = a := by
      change Fin.cycleIcc a (σ i') (σ i') = a
      exact Fin.cycleIcc_of_last hab
    have hτlt : τ i < τ i' := by
      rw [hτi, hτi']
      exact hai
    have horder (x y : Fin (n + 1)) (hx : x ≠ i') (hy : y ≠ i') :
        τ x ≤ τ y ↔ σ x ≤ σ y :=
      cycleIcc_le_iff_of_ne_last a (σ i') (σ x) (σ y) hab
        (σ.injective.ne hx) (σ.injective.ne hy)
    have horderLt (x y : Fin (n + 1)) (hx : x ≠ i') (hy : y ≠ i') :
        τ x < τ y ↔ σ x < σ y :=
      cycleIcc_lt_iff_of_ne_last a (σ i') (σ x) (σ y) hab
        (σ.injective.ne hx) (σ.injective.ne hy)
    have hpreserve (T : Finset (Fin (n + 1))) (hT : i' ∈ T → i ∈ T)
        (k : Fin (n + 1)) : IsTop τ T k ↔ IsTop σ T k := by
      by_cases hk : k = i'
      · subst k
        constructor
        · intro h
          exact ((not_le_of_gt hτlt) (h.2 i (hT h.1))).elim
        · intro h
          exact ((not_le_of_gt hσ) (h.2 i (hT h.1))).elim
      · constructor
        · rintro ⟨hkT, hmin⟩
          refine ⟨hkT, ?_⟩
          intro j hj
          by_cases hj' : j = i'
          · subst j
            exact ((horder k i hk hii').mp (hmin i (hT hj))).trans hσ.le
          · exact (horder k j hk hj').mp (hmin j hj)
        · rintro ⟨hkT, hmin⟩
          refine ⟨hkT, ?_⟩
          intro j hj
          by_cases hj' : j = i'
          · subst j
            exact ((horder k i hk hii').mpr (hmin i (hT hj))).trans hτlt.le
          · exact (horder k j hk hj').mpr (hmin j hj)
    have hnew : IsTop τ S i' := by
      refine ⟨hi', ?_⟩
      intro k hk
      by_cases hk' : k = i'
      · subst k
        exact le_rfl
      · have hik : i ≠ k := by
          intro heq
          subst k
          exact hi hk
        have hσk : σ i < σ k :=
          lt_of_le_of_ne (htop.2 k (Finset.mem_insert_of_mem hk)) (σ.injective.ne hik)
        have hτk : τ i < τ k := (horderLt i k hii' hk').mpr hσk
        rw [hτi] at hτk
        rw [hτi']
        change (σ i).val + 1 ≤ (τ k).val
        exact Nat.succ_le_iff.mpr hτk
    exact ⟨τ, hpreserve, Or.inr ⟨hnew, htop⟩⟩
  · refine ⟨σ, ?_, Or.inl ?_⟩
    · intro T hT k
      exact Iff.rfl
    · intro k
      exact isTop_insert_iff_of_not_top_insert σ S i k htop

end S02RankRobust

-- Component: P077Distribution
set_option autoImplicit false

open RankRobustAssort
open scoped BigOperators

namespace S02RankRobust

/-- Push a finite distribution forward through a map on rankings. -/
noncomputable def push {n : ℕ} (T : Ranking n → Ranking n) (lam : Ranking n → ℝ)
    (τ : Ranking n) : ℝ := by
  classical
  exact ∑ σ, if T σ = τ then lam σ else 0

/-- Reindex a finite expectation through the pushforward. -/
theorem sum_push_mul {n : ℕ} (T : Ranking n → Ranking n) (lam : Ranking n → ℝ)
    (f : Ranking n → ℝ) :
    (∑ τ, push T lam τ * f τ) = ∑ σ, lam σ * f (T σ) := by
  classical
  simp only [push, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Pushforward preserves total mass, without any injectivity requirement. -/
theorem push_total {n : ℕ} (T : Ranking n → Ranking n) (lam : Ranking n → ℝ) :
    (∑ τ, push T lam τ) = ∑ σ, lam σ := by
  simpa only [mul_one] using sum_push_mul T lam (fun _ => 1)

/-- Nonnegative masses remain nonnegative under pushforward. -/
theorem push_nonneg {n : ℕ} (T : Ranking n → Ranking n) (lam : Ranking n → ℝ)
    (hlam : ∀ σ, 0 ≤ lam σ) : ∀ τ, 0 ≤ push T lam τ := by
  classical
  intro τ
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact hlam σ
  · exact le_rfl

/-- A pushforward of a probability distribution is a probability distribution. -/
theorem isDist_push {n : ℕ} (T : Ranking n → Ranking n) {lam : Ranking n → ℝ}
    (hlam : IsDist lam) : IsDist (push T lam) := by
  refine ⟨push_nonneg T lam hlam.1, ?_⟩
  rw [push_total]
  exact hlam.2

/-- A ranking map that preserves this winner predicate preserves its probability. -/
theorem choiceProb_push {n : ℕ} (T : Ranking n → Ranking n) (lam : Ranking n → ℝ)
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (hT : ∀ σ, IsTop (T σ) S i ↔ IsTop σ S i) :
    choiceProb (push T lam) S i = choiceProb lam S i := by
  classical
  calc
    choiceProb (push T lam) S i =
        ∑ τ, push T lam τ * (if IsTop τ S i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro τ _
      simp only [mul_ite, mul_one, mul_zero]
    _ = ∑ σ, lam σ * (if IsTop (T σ) S i then 1 else 0) :=
      sum_push_mul T lam (fun τ => if IsTop τ S i then 1 else 0)
    _ = choiceProb lam S i := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [hT σ, mul_ite, mul_one, mul_zero]

/-- Historical winners determine the data constraints, so the same error vector
certifies consistency after a winner-preserving pushforward. -/
theorem consistentSet_push {n M : ℕ} (P : Problem n M)
    (T : Ranking n → Ranking n) {lam : Ranking n → ℝ}
    (hT : ∀ σ m i, IsTop (T σ) (P.S m) i ↔ IsTop σ (P.S m) i)
    (hlam : lam ∈ consistentSet P) : push T lam ∈ consistentSet P := by
  rcases hlam with ⟨hDist, ε, hε, hdata⟩
  refine ⟨isDist_push T hDist, ε, hε, ?_⟩
  intro m i hi
  rw [choiceProb_push T lam (P.S m) i (fun σ => hT σ m i)]
  exact hdata m i hi

/-- Revenue is the finite expectation of the deterministic ranking revenue. -/
theorem revenue_eq_sum_rankRevenue {n : ℕ} (r : Fin (n + 1) → ℝ)
    (lam : Ranking n → ℝ) (S : Finset (Fin (n + 1))) :
    revenue r lam S = ∑ σ, lam σ * rankRevenue r σ S := by
  classical
  unfold revenue choiceProb rankRevenue
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [mul_zero, mul_comm]

/-- A pointwise ranking comparison lifts to the corresponding distributional
comparison; the map on rankings need not be injective. -/
theorem revenue_push_le {n : ℕ} (r : Fin (n + 1) → ℝ)
    (T : Ranking n → Ranking n) (lam : Ranking n → ℝ)
    (S S' : Finset (Fin (n + 1))) (hlam : ∀ σ, 0 ≤ lam σ)
    (hpoint : ∀ σ, rankRevenue r (T σ) S ≤ rankRevenue r σ S') :
    revenue r (push T lam) S ≤ revenue r lam S' := by
  calc
    revenue r (push T lam) S = ∑ σ, lam σ * rankRevenue r (T σ) S := by
      rw [revenue_eq_sum_rankRevenue]
      exact sum_push_mul T lam (fun τ => rankRevenue r τ S)
    _ ≤ ∑ σ, lam σ * rankRevenue r σ S' := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hpoint σ) (hlam σ)
    _ = revenue r lam S' := (revenue_eq_sum_rankRevenue r lam S').symm

end S02RankRobust

-- Component: P077FiniteMax
set_option autoImplicit false

namespace S02RankRobust

/-- Among the maximizers of a function on finite sets containing an anchor,
choose one with largest cardinality. Every permitted nondecreasing insertion
must already be present in that maximizer. -/
theorem exists_optimal_closed_of_insert_mono
    {α β : Type*} [Fintype α] [DecidableEq α] [LinearOrder β]
    (z : α) (F : Finset α → β) (R : α → α → Prop)
    (hinsert : ∀ S : Finset α, z ∈ S → ∀ i i' : α,
      i ∉ S → i' ∈ S → R i' i → F S ≤ F (insert i S)) :
    ∃ S : Finset α, z ∈ S ∧
      (∀ T : Finset α, z ∈ T → F T ≤ F S) ∧
      ∀ i' ∈ S, ∀ i, R i' i → i ∈ S := by
  classical
  let A : Finset (Finset α) := Finset.univ.filter (fun S => z ∈ S)
  have hA : A.Nonempty := ⟨{z}, by simp [A]⟩
  obtain ⟨T, hT, hmaxT⟩ := A.exists_max_image F hA
  let O : Finset (Finset α) := A.filter (fun S => F T ≤ F S)
  have hO : O.Nonempty := ⟨T, by simp [O, hT]⟩
  obtain ⟨S, hS, hmaxS⟩ := O.exists_max_image Finset.card hO
  have hSA : S ∈ A := (Finset.mem_filter.mp hS).1
  have hzS : z ∈ S := (Finset.mem_filter.mp hSA).2
  have hTS : F T ≤ F S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hzS, ?_, ?_⟩
  · intro U hzU
    exact (hmaxT U (by simp [A, hzU])).trans hTS
  · intro i' hi' i hR
    by_contra hi
    have hzInsert : z ∈ insert i S := Finset.mem_insert_of_mem hzS
    have hmono : F S ≤ F (insert i S) := hinsert S hzS i i' hi hi' hR
    have hInsertO : insert i S ∈ O := by
      apply Finset.mem_filter.mpr
      exact ⟨by simp [A, hzInsert], hTS.trans hmono⟩
    have hcard : (insert i S).card ≤ S.card := hmaxS _ hInsertO
    rw [Finset.card_insert_of_notMem hi] at hcard
    exact Nat.not_succ_le_self _ hcard

end S02RankRobust

-- Component: P077Optimization
set_option autoImplicit false

namespace S02RankRobust

open RankRobustAssort

theorem revenue_coordinate_nonneg {n M : ℕ} (P : Problem n M)
    (i : Fin (n + 1)) : 0 ≤ P.r i := by
  calc
    0 = P.r 0 := P.r_zero.symm
    _ ≤ P.r i := P.r_strictMono.monotone (Fin.zero_le i)

theorem choiceProb_nonneg_of_isDist {n : ℕ}
    (lam : Equiv.Perm (Fin (n + 1)) → ℝ) (hLam : IsDist lam)
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    0 ≤ choiceProb lam S i := by
  classical
  unfold choiceProb
  apply Finset.sum_nonneg
  intro σ _
  by_cases htop : IsTop σ S i
  · simpa only [if_pos htop] using hLam.1 σ
  · simp only [if_neg htop, le_refl]

theorem revenue_nonneg_of_isDist {n M : ℕ} (P : Problem n M)
    (lam : Equiv.Perm (Fin (n + 1)) → ℝ) (hLam : IsDist lam)
    (S : Finset (Fin (n + 1))) : 0 ≤ revenue P.r lam S := by
  unfold revenue
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (revenue_coordinate_nonneg P i)
    (choiceProb_nonneg_of_isDist lam hLam S i)

/-- The revenue image is bounded below even when the assortment is empty. -/
theorem revenue_image_bddBelow {n M : ℕ} (P : Problem n M)
    (S : Finset (Fin (n + 1))) :
    BddBelow ((fun lam => revenue P.r lam S) '' consistentSet P) := by
  refine ⟨0, ?_⟩
  intro x hx
  obtain ⟨lam, hLam, rfl⟩ := hx
  exact revenue_nonneg_of_isDist P lam hLam.1 S

/-- To compare two worst cases, each model for the second assortment may use
a different consistent model for the first. No minimizing model is required. -/
theorem worstCase_le_of_transfer {n M : ℕ} (P : Problem n M)
    (hU : (consistentSet P).Nonempty) (S S' : Finset (Fin (n + 1)))
    (htransfer : ∀ lam' ∈ consistentSet P, ∃ lam ∈ consistentSet P,
      revenue P.r lam S ≤ revenue P.r lam' S') :
    worstCase P S ≤ worstCase P S' := by
  unfold worstCase
  apply le_csInf (hU.image (fun lam => revenue P.r lam S'))
  intro x hx
  obtain ⟨lam', hLam', rfl⟩ := hx
  obtain ⟨lam, hLam, hle⟩ := htransfer lam' hLam'
  exact (csInf_le (revenue_image_bddBelow P S) ⟨lam, hLam, rfl⟩).trans hle

/-- The finite optimization step: an optimal assortment with largest
cardinality is closed under every revenue-improving historical dominance move. -/
theorem exists_optimal_mem_SHat_of_insert_mono {n M : ℕ} (P : Problem n M)
    (hinsert : ∀ S : Finset (Fin (n + 1)), 0 ∈ S → ∀ i i' : Fin (n + 1),
      i ∉ S → i' ∈ S → P.r i' < P.r i → Mset P i' ⊆ Mset P i →
      worstCase P S ≤ worstCase P (insert i S)) :
    ∃ S ∈ SHat P, IsOptimalRO P S := by
  obtain ⟨S, hzero, hmax, hclosed⟩ := exists_optimal_closed_of_insert_mono
    (0 : Fin (n + 1)) (worstCase P)
    (fun i' i => P.r i' < P.r i ∧ Mset P i' ⊆ Mset P i)
    (fun S hzero i i' hi hi' hR => hinsert S hzero i i' hi hi' hR.1 hR.2)
  refine ⟨S, ⟨hzero, ?_⟩, ⟨hzero, hmax⟩⟩
  intro i' hi' i hrev hM
  exact hclosed i' hi' i ⟨hrev, hM⟩

end S02RankRobust

-- Component: P077
set_option autoImplicit false

open RankRobustAssort

namespace S02RankRobust

/-- Adding a product that dominates an existing product in revenue and in
historical availability cannot lower robust revenue. -/
theorem worstCase_insert_mono {n M : ℕ} (P : Problem n M)
    (hU : (consistentSet P).Nonempty) (S : Finset (Fin (n + 1)))
    (i i' : Fin (n + 1)) (hi : i ∉ S) (hi' : i' ∈ S)
    (hrev : P.r i' < P.r i) (hM : Mset P i' ⊆ Mset P i) :
    worstCase P S ≤ worstCase P (insert i S) := by
  classical
  have hex := fun σ : Ranking n => ranking_transfer σ S i i' hi hi'
  choose T hhistory hcase using hex
  have hpoint (σ : Ranking n) :
      rankRevenue P.r (T σ) S ≤ rankRevenue P.r σ (insert i S) := by
    rcases hcase σ with heq | htop
    · apply le_of_eq
      unfold rankRevenue
      apply Finset.sum_congr rfl
      intro k _
      rw [heq k]
    · rw [rankRevenue_of_top htop.1, rankRevenue_of_top htop.2]
      exact hrev.le
  have hhistorical (σ : Ranking n) (m : Fin M) (k : Fin (n + 1)) :
      IsTop (T σ) (P.S m) k ↔ IsTop σ (P.S m) k := by
    apply hhistory σ (P.S m) _ k
    intro hm
    have hm' : m ∈ Mset P i' := by simpa [Mset] using hm
    simpa [Mset] using hM hm'
  apply worstCase_le_of_transfer P hU S (insert i S)
  intro lam hlam
  refine ⟨push T lam, consistentSet_push P T hhistorical hlam, ?_⟩
  exact revenue_push_le P.r T lam S (insert i S) hlam.1.1 hpoint

end S02RankRobust

/-- Some globally optimal robust assortment is revenue-ordered relative to all
historical assortments, for the full published class of problem instances. -/
theorem solution {n M : ℕ} (P : Problem n M) (hU : (consistentSet P).Nonempty) :
    ∃ S ∈ SHat P, IsOptimalRO P S := by
  apply S02RankRobust.exists_optimal_mem_SHat_of_insert_mono P
  intro S _ i i' hi hi' hrev hM
  exact S02RankRobust.worstCase_insert_mono P hU S i i' hi hi' hrev hM

#print axioms solution
