-- Prove2me | solution 1 for ShapleyScarf.Balanced.marketGame_isNTUGame
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:16:34.876839+00:00
-- url     : https://prove2.me/submissions/04f0386a-4e3e-4e75-8f77-f94c73bd863f

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame
import Definitions.Def_ShapleyScarf_Balanced_NTUGame



namespace ShapleyScarf.Balanced

lemma ss_rowsum {N : Type*} [Fintype N] [DecidableEq N] {S : Finset N} {P : Matrix N N ℝ}
    (h : IsSPermutation S P) : ∀ i ∈ S, ∑ j, P i j = 1 := by
  obtain ⟨⟨h01, hcol, hrow, hcol0⟩, hle⟩ := h
  have h1 : ∑ i, ∑ j, P i j = (S.card : ℝ) := by
    rw [Finset.sum_comm (f := fun i j => P i j)]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · rw [Finset.sum_congr rfl hcol]; simp
    · intro j _ hj; exact Finset.sum_eq_zero (fun i _ => hcol0 j hj i)
  have h2 : ∑ i ∈ S, ∑ j, P i j = ∑ i, ∑ j, P i j := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi; exact Finset.sum_eq_zero (fun j _ => hrow i hi j)
  have h3 : ∑ i ∈ S, ∑ j, P i j = ∑ i ∈ S, (1:ℝ) := by
    rw [h2, h1]; simp
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 h3

lemma ss_mem_iff {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) (S : Finset N)
    (x : N → ℝ) : x ∈ marketGame A S ↔ ∃ P : Matrix N N ℝ, IsSPermutation S P ∧
      ∀ i j, P i j = 1 → i ∈ S ∧ x i ≤ A i j := by
  constructor
  · rintro ⟨P, hP, hle⟩
    refine ⟨P, hP, fun i j h => ?_⟩
    have := hle i j
    rw [h] at this
    by_contra hc
    simp [acceptableMatrix, hc] at this
    linarith
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, fun i j => ?_⟩
    rcases hP.1.1 i j with h0 | h1
    · rw [h0]; simp only [acceptableMatrix]; split_ifs <;> norm_num
    · rw [h1]; simp [acceptableMatrix, h i j h1]

/-- identity permutation of S -/
def ssId {N : Type*} [DecidableEq N] (S : Finset N) : Matrix N N ℝ :=
  fun a b => if a ∈ S ∧ a = b then 1 else 0

lemma ssId_perm {N : Type*} [Fintype N] [DecidableEq N] (S : Finset N) :
    IsSPermutation S (ssId S) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j; unfold ssId; split_ifs <;> simp
  · intro j hj
    unfold ssId
    have : ∀ i, (if i ∈ S ∧ i = j then (1:ℝ) else 0) = if i = j then 1 else 0 := by
      intro i; by_cases h : i = j
      · subst h; simp [hj]
      · simp [h]
    simp [this]
  · intro i hi j; unfold ssId; simp [hi]
  · intro j hj i; unfold ssId
    by_cases h : i = j
    · subst h; simp [hj]
    · simp [h]
  · intro i; unfold ssId
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi]

lemma ss_single {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) (i : N) (x : N → ℝ) :
    x ∈ marketGame A {i} ↔ x i ≤ A i i := by
  rw [ss_mem_iff]
  constructor
  · rintro ⟨P, hP, h⟩
    have h1 := ss_rowsum hP i (Finset.mem_singleton_self i)
    obtain ⟨j, hj⟩ : ∃ j, P i j = 1 := by
      by_contra hc
      push_neg at hc
      have : ∀ j, P i j = 0 := fun j => (hP.1.1 i j).resolve_right (hc j)
      simp [this] at h1
    have hjS : j ∈ ({i} : Finset N) := by
      by_contra hc
      have := hP.1.2.2.2 j hc i
      rw [this] at hj; norm_num at hj
    have hji : j = i := by simpa using hjS
    have := (h i j hj).2
    rwa [hji] at this
  · intro hx
    refine ⟨ssId {i}, ssId_perm _, fun a b hab => ?_⟩
    unfold ssId at hab
    by_cases h : a ∈ ({i} : Finset N) ∧ a = b
    · obtain ⟨ha, rfl⟩ := h
      have : a = i := by simpa using ha
      subst this
      exact ⟨ha, hx⟩
    · rw [if_neg h] at hab; norm_num at hab

lemma ss_interior_single {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) (i : N) :
    interior (marketGame A {i}) = {x | x i < A i i} := by
  have : marketGame A {i} = (fun x : N → ℝ => x i) ⁻¹' Set.Iic (A i i) := by
    ext x; simp [ss_single]
  rw [this, ← (isOpenMap_eval i).preimage_interior_eq_interior_preimage (continuous_apply i),
    interior_Iic]
  rfl

lemma ss_isNTU {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) :
    IsNTUGame (marketGame A) := by
  intro S hS
  have hmem := ss_mem_iff A S
  have hUn : ∀ x, x ∈ singletonInteriorUnion (marketGame A) S ↔ ∃ i ∈ S, x i < A i i := by
    intro x
    simp only [singletonInteriorUnion, Set.mem_iUnion, Finset.mem_coe, ss_interior_single,
      Set.mem_setOf_eq, exists_prop]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- closed
    have hF : {P : Matrix N N ℝ | IsSPermutation S P}.Finite := by
      let f : Matrix N N ℝ → (N → N → Bool) := fun P i j => decide (P i j = 1)
      refine Set.Finite.of_injOn (f := f) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
        Set.finite_univ
      intro P hP Q hQ hPQ
      ext i j
      have := congrFun (congrFun hPQ i) j
      simp only [f, decide_eq_decide] at this
      rcases hP.1.1 i j with h | h <;> rcases hQ.1.1 i j with h' | h' <;>
        simp_all
    have : marketGame A S = ⋃ P ∈ {P : Matrix N N ℝ | IsSPermutation S P},
        {x : N → ℝ | ∀ i j, P i j = 1 → i ∈ S ∧ x i ≤ A i j} := by
      ext x; rw [hmem]; simp
    rw [this]
    refine hF.isClosed_biUnion (fun P _ => ?_)
    have hc : ∀ i j, IsClosed {x : N → ℝ | P i j = 1 → i ∈ S ∧ x i ≤ A i j} := by
      intro i j
      by_cases hp : P i j = 1
      · by_cases hi : i ∈ S
        · have : {x : N → ℝ | P i j = 1 → i ∈ S ∧ x i ≤ A i j} = {x | x i ≤ A i j} := by
            ext x; simp [hp, hi]
          rw [this]
          exact isClosed_le (continuous_apply i : Continuous fun x : N → ℝ => x i) continuous_const
        · have : {x : N → ℝ | P i j = 1 → i ∈ S ∧ x i ≤ A i j} = ∅ := by
            ext x; simp [hp, hi]
          rw [this]; exact isClosed_empty
      · have : {x : N → ℝ | P i j = 1 → i ∈ S ∧ x i ≤ A i j} = Set.univ := by
          ext x; simp [hp]
        rw [this]; exact isClosed_univ
    have : {x : N → ℝ | ∀ i j, P i j = 1 → i ∈ S ∧ x i ≤ A i j} =
        ⋂ i, ⋂ j, {x : N → ℝ | P i j = 1 → i ∈ S ∧ x i ≤ A i j} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => hc i j
  · intro x y hx hy
    rw [hmem] at hx ⊢
    obtain ⟨P, hP, h⟩ := hx
    refine ⟨P, hP, fun i j hij => ?_⟩
    obtain ⟨hi, hxl⟩ := h i j hij
    exact ⟨hi, (hy i hi).trans hxl⟩
  · -- bounded
    rw [isBounded_iff_forall_norm_le]
    refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
    rintro x ⟨⟨hx, hnot⟩, hslice⟩
    have hM : 0 ≤ ∑ i, ∑ j, |A i j| :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
    have hle : ∀ i j, |A i j| ≤ ∑ i, ∑ j, |A i j| := by
      intro i j
      calc |A i j| ≤ ∑ j, |A i j| :=
            Finset.single_le_sum (f := fun j => |A i j|) (fun j _ => abs_nonneg _)
              (Finset.mem_univ j)
        _ ≤ ∑ i, ∑ j, |A i j| :=
            Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
              (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)
    refine (pi_norm_le_iff_of_nonneg hM).2 (fun i => ?_)
    rw [Real.norm_eq_abs]
    by_cases hi : i ∈ S
    · have h1 : A i i ≤ x i := by
        by_contra hc
        push_neg at hc
        exact hnot ((hUn x).2 ⟨i, hi, hc⟩)
      rw [hmem] at hx
      obtain ⟨P, hP, h⟩ := hx
      have hr := ss_rowsum hP i hi
      obtain ⟨j, hj⟩ : ∃ j, P i j = 1 := by
        by_contra hc
        push_neg at hc
        have : ∀ j, P i j = 0 := fun j => (hP.1.1 i j).resolve_right (hc j)
        simp [this] at hr
      have h2 := (h i j hj).2
      rw [abs_le]
      have a1 := hle i i
      have a2 := hle i j
      have a3 := neg_abs_le (A i i)
      have a4 := le_abs_self (A i j)
      constructor <;> linarith
    · rw [hslice i hi]; simpa using hM
  · refine ⟨fun i => if i ∈ S then A i i else 0, ⟨?_, ?_⟩, ?_⟩
    · rw [hmem]
      refine ⟨ssId S, ssId_perm S, fun a b hab => ?_⟩
      unfold ssId at hab
      by_cases h : a ∈ S ∧ a = b
      · obtain ⟨ha, rfl⟩ := h
        simp [ha]
      · rw [if_neg h] at hab; norm_num at hab
    · rw [hUn]
      rintro ⟨i, hi, h⟩
      simp [hi] at h
    · intro j hj; simp [hj]

lemma ss_B_eq {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) (T : Finset (Finset N))
    (x : N → ℝ) (δ : Finset N → ℝ) (hδ : IsBalancingWeights T δ) :
    acceptableMatrix A Finset.univ x = ∑ S ∈ T, δ S • acceptableMatrix A S x := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, acceptableMatrix]
  have h := hδ.2.2 i
  by_cases hx : x i ≤ A i j
  · simp only [hx, and_true, Finset.mem_univ, true_and, mul_ite, mul_one, mul_zero]
    exact h.symm
  · simp [hx]

lemma ss_rowsum_zero {N : Type*} [Fintype N] [DecidableEq N] {S : Finset N} {P : Matrix N N ℝ}
    (h : IsSPermutation S P) : ∀ i ∉ S, ∑ j, P i j = 0 := by
  intro i hi
  exact Finset.sum_eq_zero (fun j _ => h.1.2.2.1 i hi j)

lemma ss_doublyStochastic {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (T : Finset (Finset N)) (δ : Finset N → ℝ) (P : Finset N → Matrix N N ℝ)
    (hδ : IsBalancingWeights T δ) (hP : ∀ S ∈ T, IsSPermutation S (P S)) :
    (∑ S ∈ T, δ S • P S) ∈ doublyStochastic ℝ N := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.sum_apply]
    refine Finset.sum_nonneg (fun S hS => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    refine mul_nonneg (hδ.1 S) ?_
    rcases (hP S hS).1.1 i j with h | h <;> rw [h] <;> norm_num
  · intro i
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← hδ.2.2 i]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    by_cases hi : i ∈ S
    · rw [ss_rowsum (hP S hS) i hi]; simp [hi]
    · rw [ss_rowsum_zero (hP S hS) i hi]; simp [hi]
  · intro j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← hδ.2.2 j]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    by_cases hj : j ∈ S
    · rw [(hP S hS).1.2.1 j hj]; simp [hj]
    · rw [Finset.sum_eq_zero (fun i _ => (hP S hS).1.2.2.2 j hj i)]; simp [hj]

lemma ss_perm_entry {N : Type*} [Fintype N] [DecidableEq N] (σ : Equiv.Perm N) (i j : N) :
    σ.permMatrix ℝ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma ss_perm_isS {N : Type*} [Fintype N] [DecidableEq N] (σ : Equiv.Perm N) :
    IsSPermutation Finset.univ (σ.permMatrix ℝ) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j; rw [ss_perm_entry]; split_ifs <;> simp
  · intro j _
    simp_rw [ss_perm_entry]
    rw [Equiv.sum_comp σ (fun k => if k = j then (1:ℝ) else 0)]
    simp
  · intro i hi; exact absurd (Finset.mem_univ i) hi
  · intro j hj; exact absurd (Finset.mem_univ j) hj
  · intro i
    simp_rw [ss_perm_entry]
    simp

lemma ss_birkhoff {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) (x : N → ℝ) (D : Matrix N N ℝ)
    (hD : D ∈ doublyStochastic ℝ N)
    (hDB : ∀ i j, D i j ≤ acceptableMatrix A Finset.univ x i j) :
    ∃ P : Matrix N N ℝ, IsSPermutation Finset.univ P ∧
      ∀ i j, P i j ≤ acceptableMatrix A Finset.univ x i j := by
  set B := acceptableMatrix A Finset.univ x with hB
  have hB01 : ∀ i j, B i j = 0 ∨ B i j = 1 := by
    intro i j; simp only [hB, acceptableMatrix]; split_ifs <;> simp
  by_contra hcon
  push_neg at hcon
  let f : Matrix N N ℝ → ℝ := fun M => ∑ i, ∑ j, if B i j = 0 then M i j else 0
  have hf : IsLinearMap ℝ f := by
    refine ⟨fun a b => ?_, fun c a => ?_⟩
    · simp only [f, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      split_ifs <;> simp
    · simp only [f, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      split_ifs <;> simp
  have hsub : {M : Matrix N N ℝ | ∃ σ : Equiv.Perm N, σ.permMatrix ℝ = M} ⊆ {M | 1 ≤ f M} := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨i, j, hij⟩ := hcon _ (ss_perm_isS σ)
    have hBij : B i j = 0 := by
      rcases hB01 i j with h | h
      · exact h
      · rw [h] at hij
        rw [ss_perm_entry] at hij
        split_ifs at hij <;> linarith
    have hP1 : σ.permMatrix ℝ i j = 1 := by
      rw [ss_perm_entry] at hij ⊢
      split_ifs at hij ⊢ <;> first | rfl | (exfalso; linarith)
    show 1 ≤ ∑ i, ∑ j, if B i j = 0 then σ.permMatrix ℝ i j else 0
    have hnn : ∀ i j, 0 ≤ σ.permMatrix ℝ i j := by
      intro i j; rw [ss_perm_entry]; split_ifs <;> norm_num
    calc (1:ℝ) = (if B i j = 0 then σ.permMatrix ℝ i j else 0) := by rw [if_pos hBij, hP1]
      _ ≤ ∑ j, if B i j = 0 then σ.permMatrix ℝ i j else 0 :=
          Finset.single_le_sum (f := fun j => if B i j = 0 then σ.permMatrix ℝ i j else 0)
            (fun j _ => by split_ifs; exacts [hnn _ _, le_rfl]) (Finset.mem_univ j)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun i => ∑ j, if B i j = 0 then σ.permMatrix ℝ i j else 0)
            (fun i _ => Finset.sum_nonneg (fun j _ => by split_ifs; exacts [hnn _ _, le_rfl]))
            (Finset.mem_univ i)
  have hcv : Convex ℝ {M : Matrix N N ℝ | 1 ≤ f M} := convex_halfSpace_ge hf 1
  have hmem : D ∈ convexHull ℝ {M : Matrix N N ℝ | ∃ σ : Equiv.Perm N, σ.permMatrix ℝ = M} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hD
  have := convexHull_min hsub hcv hmem
  have h0 : f D = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    split_ifs with h
    · have := hDB i j
      rw [h] at this
      have := (mem_doublyStochastic_iff_sum.1 hD).1 i j
      linarith [hDB i j]
    · rfl
  have : (1:ℝ) ≤ 0 := by rw [← h0]; exact this
  linarith

theorem ss_balanced {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) : IsBalancedGame (marketGame A) := by
  refine ⟨ss_isNTU A, fun T hT x hx => ?_⟩
  obtain ⟨_, δ, hδ⟩ := hT
  choose! P hP using fun S (hS : S ∈ T) => (hx S hS)
  have hDS := ss_doublyStochastic T δ P hδ (fun S hS => (hP S hS).1)
  have hB := ss_B_eq A T x δ hδ
  obtain ⟨Q, hQ, hQle⟩ := ss_birkhoff A x _ hDS (fun i j => by
    rw [hB, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_le_sum (fun S hS => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left ((hP S hS).2 i j) (hδ.1 S))
  exact ⟨Q, hQ, hQle⟩

end ShapleyScarf.Balanced

open ShapleyScarf.Balanced


theorem solution {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) : IsNTUGame (marketGame A) := by
  exact ss_isNTU A
