-- Prove2me | solution 1 for ShapleyScarf.CoreExistence.marketGame_balanced_nonempty_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T00:24:08.245783+00:00
-- url     : https://prove2.me/submissions/6e332a22-0673-4ffe-9593-aecc01dac06b

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_MarketGame
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_CoreExistence_payoffCore
import Definitions.Def_ShapleyScarf_CoreExistence_assignmentPayoff

set_option autoImplicit false

namespace SSProof

open ShapleyScarf.Balanced

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Entries of an acceptable matrix are 0 or 1. -/
lemma acc_nonneg (A : N → N → ℝ) (S : Finset N) (x : N → ℝ) (i j : N) :
    0 ≤ acceptableMatrix A S x i j := by
  unfold acceptableMatrix; split_ifs <;> norm_num

lemma acc_of_one_le (A : N → N → ℝ) (S : Finset N) (x : N → ℝ) (i j : N)
    (h : 1 ≤ acceptableMatrix A S x i j) : i ∈ S ∧ x i ≤ A i j := by
  unfold acceptableMatrix at h
  split_ifs at h with hc
  · exact hc
  · norm_num at h

/-- A bijection preserving `S` yields membership in the market game. -/
lemma mem_marketGame_of_bij (A : N → N → ℝ) (S : Finset N) (σ : N → N)
    (hσ : Function.Bijective σ) (hS : ∀ i, i ∈ S ↔ σ i ∈ S) (x : N → ℝ)
    (hx : ∀ i ∈ S, x i ≤ A i (σ i)) : x ∈ marketGame A S := by
  refine ⟨fun i j => if i ∈ S ∧ σ i = j then 1 else 0, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro i j; dsimp only; split_ifs <;> simp
  · intro j hj
    obtain ⟨i0, hi0⟩ := hσ.2 j
    have hi0S : i0 ∈ S := (hS i0).2 (hi0 ▸ hj)
    rw [Finset.sum_eq_single i0]
    · simp [hi0S, hi0]
    · intro b _ hb
      have : σ b ≠ j := fun h => hb (hσ.1 (h.trans hi0.symm))
      simp [this]
    · simp
  · intro i hi j; simp [hi]
  · intro j hj i
    by_cases hi : i ∈ S
    · have : σ i ≠ j := fun h => hj (h ▸ (hS i).1 hi)
      simp [this]
    · simp [hi]
  · intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi]
  · intro i j
    show (if i ∈ S ∧ σ i = j then (1:ℝ) else 0) ≤ acceptableMatrix A S x i j
    by_cases h : i ∈ S ∧ σ i = j
    · rw [if_pos h]
      unfold acceptableMatrix
      rw [if_pos ⟨h.1, h.2 ▸ hx i h.1⟩]
    · rw [if_neg h]; exact acc_nonneg A S x i j

lemma rowsum_of_SPerm (S : Finset N) (P : Matrix N N ℝ) (hP : IsSPermutation S P) (i : N) :
    ∑ j, P i j = if i ∈ S then 1 else 0 := by
  obtain ⟨⟨h01, hcol, hrow0, hcol0⟩, hrow⟩ := hP
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have htot : ∑ i ∈ S, ∑ j, P i j = ∑ i ∈ S, (1 : ℝ) := by
      have e1 : ∑ i ∈ S, ∑ j, P i j = ∑ i, ∑ j, P i j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        simp [hrow0 k hk]
      have e2 : ∑ j, ∑ i, P i j = ∑ j ∈ S, ∑ i, P i j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        simp [hcol0 k hk]
      rw [e1, show (∑ i, ∑ j, P i j) = ∑ j, ∑ i, P i j from Finset.sum_comm, e2]
      exact Finset.sum_congr rfl (fun j hj => hcol j hj)
    exact ((Finset.sum_eq_sum_iff_of_le (fun k _ => hrow k)).1 htot) i hi
  · rw [if_neg hi]; simp [hrow0 i hi]

lemma colsum_of_SPerm (S : Finset N) (P : Matrix N N ℝ) (hP : IsSPermutation S P) (j : N) :
    ∑ i, P i j = if j ∈ S then 1 else 0 := by
  obtain ⟨⟨_, hcol, _, hcol0⟩, _⟩ := hP
  by_cases hj : j ∈ S
  · rw [if_pos hj]; exact hcol j hj
  · rw [if_neg hj]; simp [hcol0 j hj]

/-- Membership in `V(S)` yields an `S`-reshuffling meeting the thresholds. -/
lemma exists_tau (A : N → N → ℝ) (S : Finset N) (x : N → ℝ) (hx : x ∈ marketGame A S) :
    ∃ τ : N → N, (∀ i ∈ S, τ i ∈ S) ∧ ∀ i ∈ S, x i ≤ A i (τ i) := by
  obtain ⟨P, hP, hle⟩ := hx
  have key : ∀ i, ∃ j, i ∈ S → (j ∈ S ∧ x i ≤ A i j) := by
    intro i
    by_cases hi : i ∈ S
    · have hs := rowsum_of_SPerm S P hP i
      rw [if_pos hi] at hs
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hs]; norm_num :
        ∑ j, P i j ≠ 0)
      have hPj : P i j = 1 := (hP.1.1 i j).resolve_left hj
      refine ⟨j, fun _ => ⟨?_, (acc_of_one_le A S x i j (hPj ▸ hle i j)).2⟩⟩
      by_contra hjS
      exact hj (hP.1.2.2.2 j hjS i)
    · exact ⟨i, fun h => absurd h hi⟩
  choose τ hτ using key
  exact ⟨τ, fun i hi => (hτ i hi).1, fun i hi => (hτ i hi).2⟩

lemma interior_sub (A : N → N → ℝ) (S : Finset N) (y : N → ℝ)
    (hy : y ∈ interior (marketGame A S)) :
    ∃ τ : N → N, (∀ i ∈ S, τ i ∈ S) ∧ ∀ i ∈ S, y i < A i (τ i) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
  obtain ⟨ε, hε, hball⟩ := hy
  have hz : (fun k => y k + ε / 2) ∈ marketGame A S := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro k
    rw [Real.dist_eq]
    have : y k + ε / 2 - y k = ε / 2 := by ring
    rw [this, abs_of_pos (by linarith)]
    linarith
  obtain ⟨τ, hτS, hτ⟩ := exists_tau A S _ hz
  refine ⟨τ, hτS, fun i hi => ?_⟩
  have h' : y i + ε / 2 ≤ A i (τ i) := hτ i hi
  linarith

/-- Top trading cycles, as a strong induction on the set of remaining traders. -/
lemma ttc (A : N → N → ℝ) : ∀ R : Finset N, ∃ σ : N → N, Set.MapsTo σ R R ∧ Set.InjOn σ R ∧
    ∀ S : Finset N, S ⊆ R → S.Nonempty → ∀ τ : N → N, (∀ i ∈ S, τ i ∈ S) →
      ∃ i ∈ S, A i (τ i) ≤ A i (σ i) := by
  classical
  intro R
  induction R using Finset.strongInduction
  rename_i R ih
  rcases R.eq_empty_or_nonempty with hR | ⟨r0, hr0⟩
  · subst hR
    refine ⟨id, by simp, by simp, fun S hS hne => ?_⟩
    rw [Finset.subset_empty] at hS
    subst hS
    exact absurd hne Finset.not_nonempty_empty
  have hmax : ∀ i, ∃ j ∈ R, ∀ k ∈ R, A i k ≤ A i j := fun i =>
    R.exists_max_image (A i) ⟨r0, hr0⟩
  choose f hfR hfmax using hmax
  -- periodic points of `f` lie in `R`
  have hperR : ∀ x ∈ Function.periodicPts f, x ∈ R := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have : f^[m + 1] x = x := hxn
    rw [Function.iterate_succ_apply'] at this
    rw [← this]; exact hfR _
  -- a periodic point exists
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] r0)
  have hper : ∃ x, x ∈ Function.periodicPts f := by
    rcases lt_or_gt_of_ne hab with h | h
    · refine ⟨f^[a] r0, Function.mk_mem_periodicPts (n := b - a) (by omega) ?_⟩
      show f^[b - a] (f^[a] r0) = f^[a] r0
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq.symm
    · refine ⟨f^[b] r0, Function.mk_mem_periodicPts (n := a - b) (by omega) ?_⟩
      show f^[a - b] (f^[b] r0) = f^[b] r0
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq
  obtain ⟨x0, hx0⟩ := hper
  set R' := R.filter (fun x => x ∉ Function.periodicPts f) with hR'
  have hss : R' ⊂ R := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨x0, hperR x0 hx0, by simp [hR', hx0]⟩
  obtain ⟨σ', hmap', hinj', hcore'⟩ := ih R' hss
  have hbij := Function.bijOn_periodicPts f
  refine ⟨fun i => if i ∈ Function.periodicPts f then f i else σ' i, ?_, ?_, ?_⟩
  · intro i hi
    simp only
    split_ifs with hp
    · exact hfR i
    · have : i ∈ R' := by simp [hR', Finset.mem_coe.1 hi, hp]
      exact Finset.filter_subset _ _ (hmap' this)
  · intro i hi j hj hij
    simp only at hij
    by_cases hpi : i ∈ Function.periodicPts f <;> by_cases hpj : j ∈ Function.periodicPts f
    · rw [if_pos hpi, if_pos hpj] at hij
      exact hbij.injOn hpi hpj hij
    · rw [if_pos hpi, if_neg hpj] at hij
      have hjR' : j ∈ R' := by simp [hR', Finset.mem_coe.1 hj, hpj]
      have h1 := hbij.mapsTo hpi
      have h2 := hmap' hjR'
      rw [← hij] at h2
      simp [hR'] at h2
      exact absurd h1 h2.2
    · rw [if_neg hpi, if_pos hpj] at hij
      have hiR' : i ∈ R' := by simp [hR', Finset.mem_coe.1 hi, hpi]
      have h1 := hbij.mapsTo hpj
      have h2 := hmap' hiR'
      rw [hij] at h2
      simp [hR'] at h2
      exact absurd h1 h2.2
    · rw [if_neg hpi, if_neg hpj] at hij
      have hiR' : i ∈ R' := by simp [hR', Finset.mem_coe.1 hi, hpi]
      have hjR' : j ∈ R' := by simp [hR', Finset.mem_coe.1 hj, hpj]
      exact hinj' hiR' hjR' hij
  · intro S hS hne τ hτ
    by_cases h : ∃ i ∈ S, i ∈ Function.periodicPts f
    · obtain ⟨i, hiS, hip⟩ := h
      refine ⟨i, hiS, ?_⟩
      simp only [if_pos hip]
      exact hfmax i (τ i) (hS (hτ i hiS))
    · push Not at h
      have hS' : S ⊆ R' := by
        intro i hi
        simp [hR', hS hi, h i hi]
      obtain ⟨i, hiS, hle⟩ := hcore' S hS' hne τ hτ
      refine ⟨i, hiS, ?_⟩
      simp only [if_neg (h i hiS)]
      exact hle

lemma ntu (A : N → N → ℝ) : IsNTUGame (marketGame A) := by
  intro S _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hfin : {P : Matrix N N ℝ | IsSPermutation S P}.Finite := by
      apply (Set.finite_range (fun b : N → N → Bool =>
        (fun i j => if b i j then (1:ℝ) else 0 : Matrix N N ℝ))).subset
      intro P hP
      refine ⟨fun i j => decide (P i j = 1), ?_⟩
      ext i j
      rcases hP.1.1 i j with h | h <;> simp [h]
    have heq : marketGame A S = ⋃ P ∈ {P : Matrix N N ℝ | IsSPermutation S P},
        ⋂ i, ⋂ j, {x : N → ℝ | P i j ≤ acceptableMatrix A S x i j} := by
      ext x; simp [marketGame]
    rw [heq]
    refine hfin.isClosed_biUnion (fun P hP => isClosed_iInter (fun i => isClosed_iInter (fun j => ?_)))
    rcases hP.1.1 i j with h | h
    · rw [h]
      convert isClosed_univ
      ext x; simp [acc_nonneg]
    · rw [h]
      by_cases hi : i ∈ S
      · have e : {x : N → ℝ | (1:ℝ) ≤ acceptableMatrix A S x i j} = {x | x i ≤ A i j} := by
          ext x
          simp only [Set.mem_setOf_eq, acceptableMatrix]
          by_cases hx : x i ≤ A i j <;> simp [hi, hx]
        rw [e]; exact isClosed_le (continuous_apply i) continuous_const
      · convert isClosed_empty
        ext x; simp [acceptableMatrix, hi]
  · intro x y hx hy
    obtain ⟨P, hP, hle⟩ := hx
    refine ⟨P, hP, fun i j => ?_⟩
    have := hle i j
    unfold acceptableMatrix at this ⊢
    by_cases hc : i ∈ S ∧ x i ≤ A i j
    · rw [if_pos ⟨hc.1, (hy i hc.1).trans hc.2⟩]; rwa [if_pos hc] at this
    · rw [if_neg hc] at this; split_ifs <;> linarith
  · apply (Metric.isBounded_Icc (fun i => if i ∈ S then A i i else 0)
      (fun i => if i ∈ S then ∑ j, |A i j| else 0)).subset
    rintro x ⟨⟨hxV, hxI⟩, hxS⟩
    obtain ⟨τ, _, hτ⟩ := exists_tau A S x hxV
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hi : i ∈ S
      · simp only [if_pos hi]
        by_contra hlt
        push Not at hlt
        apply hxI
        simp only [singletonInteriorUnion, Set.mem_iUnion]
        refine ⟨i, Finset.mem_coe.2 hi, ?_⟩
        refine interior_maximal (t := {y : N → ℝ | y i < A i i}) (fun y hy => ?_)
          (isOpen_lt (continuous_apply i) continuous_const) hlt
        refine mem_marketGame_of_bij A {i} id Function.bijective_id (by simp) y ?_
        intro k hk
        rw [Finset.mem_singleton] at hk
        subst hk
        exact le_of_lt hy
      · simp [if_neg hi, hxS i hi]
    · by_cases hi : i ∈ S
      · simp only [if_pos hi]
        calc x i ≤ A i (τ i) := hτ i hi
          _ ≤ |A i (τ i)| := le_abs_self _
          _ ≤ ∑ j, |A i j| := Finset.single_le_sum (f := fun j => |A i j|)
              (fun j _ => abs_nonneg _) (Finset.mem_univ _)
      · simp [if_neg hi, hxS i hi]
  · refine ⟨fun i => if i ∈ S then A i i else 0, ⟨?_, ?_⟩, ?_⟩
    · apply mem_marketGame_of_bij A S id Function.bijective_id (by simp)
      intro i hi; simp [hi]
    · intro hU
      simp only [singletonInteriorUnion, Set.mem_iUnion] at hU
      obtain ⟨i, hi, hint⟩ := hU
      obtain ⟨τ, hτS, hτ⟩ := interior_sub A {i} _ hint
      have h1 := hτ i (Finset.mem_singleton_self i)
      have h2 : τ i = i := Finset.mem_singleton.1 (hτS i (Finset.mem_singleton_self i))
      rw [h2] at h1
      simp [Finset.mem_coe.1 hi] at h1
    · intro j hj; simp [hj]

lemma balanced (A : N → N → ℝ) (T : Finset (Finset N)) (hT : IsBalancedFamily T)
    (x : N → ℝ) (hx : ∀ S ∈ T, x ∈ marketGame A S) : x ∈ marketGame A Finset.univ := by
  classical
  obtain ⟨_, δ, hδ0, _, hδ1⟩ := hT
  have hex : ∀ S, ∃ P : Matrix N N ℝ, S ∈ T →
      (IsSPermutation S P ∧ ∀ i j, P i j ≤ acceptableMatrix A S x i j) := by
    intro S
    by_cases hS : S ∈ T
    · obtain ⟨P, hP⟩ := hx S hS; exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose P hP using hex
  set Q : Matrix N N ℝ := ∑ S ∈ T, δ S • P S with hQ
  have hQij : ∀ i j, Q i j = ∑ S ∈ T, δ S * P S i j := by
    intro i j; simp [hQ, Matrix.sum_apply]
  have hPnn : ∀ S ∈ T, ∀ i j, 0 ≤ P S i j := fun S hS i j => by
    rcases (hP S hS).1.1.1 i j with h | h <;> rw [h] <;> norm_num
  have hQds : Q ∈ doublyStochastic ℝ N := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · rw [hQij]; exact Finset.sum_nonneg (fun S hS => mul_nonneg (hδ0 S) (hPnn S hS i j))
    · simp_rw [hQij]
      rw [Finset.sum_comm, ← hδ1 i]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [← Finset.mul_sum, rowsum_of_SPerm S (P S) (hP S hS).1 i]
      split_ifs <;> simp
    · simp_rw [hQij]
      rw [Finset.sum_comm, ← hδ1 j]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [← Finset.mul_sum, colsum_of_SPerm S (P S) (hP S hS).1 j]
      split_ifs <;> simp
  obtain ⟨w, hw0, hw1, hwQ⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hQds
  obtain ⟨σ, hσ⟩ : ∃ σ, 0 < w σ := by
    by_contra h
    push Not at h
    have : ∑ σ, w σ ≤ 0 := Finset.sum_nonpos (fun σ _ => h σ)
    linarith
  apply mem_marketGame_of_bij A _ σ σ.bijective (by simp) x
  intro i _
  have hpos : 0 < Q i (σ i) := by
    rw [← hwQ]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    calc (0:ℝ) < w σ * σ.permMatrix ℝ i (σ i) := by
          simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]; exact hσ
      _ ≤ ∑ τ, w τ * τ.permMatrix ℝ i (σ i) :=
          Finset.single_le_sum (f := fun τ => w τ * τ.permMatrix ℝ i (σ i))
            (fun τ _ => mul_nonneg (hw0 τ)
              (nonneg_of_mem_doublyStochastic permMatrix_mem_doublyStochastic))
            (Finset.mem_univ σ)
  rw [hQij] at hpos
  obtain ⟨S, hS, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hP1 : P S i (σ i) = 1 :=
    ((hP S hS).1.1.1 i (σ i)).resolve_left (fun h => hne (by rw [h, mul_zero]))
  exact (acc_of_one_le A S x i (σ i) (hP1 ▸ (hP S hS).2 i (σ i))).2

end SSProof

open ShapleyScarf.CoreExistence in
theorem solution
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) :
    ShapleyScarf.Balanced.IsBalancedGame (ShapleyScarf.Balanced.marketGame A) ∧
      (payoffCore (ShapleyScarf.Balanced.marketGame A)).Nonempty ∧
      ∃ σ : N → N, Function.Bijective σ ∧
        assignmentPayoff A σ ∈ payoffCore (ShapleyScarf.Balanced.marketGame A) ∧
        ShapleyScarf.TopTrading.IsCoreAllocation A σ := by
  obtain ⟨σ, _, hinj, hcore⟩ := SSProof.ttc A Finset.univ
  have hσinj : Function.Injective σ := fun a b h => hinj (by simp) (by simp) h
  have hσ : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  have hcoreσ : assignmentPayoff A σ ∈ payoffCore (ShapleyScarf.Balanced.marketGame A) := by
    refine ⟨SSProof.mem_marketGame_of_bij A _ σ hσ (by simp) _ (fun i _ => le_refl _), ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro S hS hint
    obtain ⟨τ, hτS, hτ⟩ := SSProof.interior_sub A S _ hint
    obtain ⟨i, hi, hle⟩ := hcore S (Finset.subset_univ _) hS τ hτS
    have := hτ i hi
    simp only [assignmentPayoff] at this
    linarith
  refine ⟨⟨SSProof.ntu A, fun T hT x hx => SSProof.balanced A T hT x hx⟩, ⟨_, hcoreσ⟩,
    σ, hσ, hcoreσ, hσ, ?_⟩
  rintro ⟨S, τ, hne, hτS, _, hlt⟩
  obtain ⟨i, hi, hle⟩ := hcore S (Finset.subset_univ _) hne τ hτS
  linarith [hlt i hi]
