-- Prove2me | solution 1 for SP4FiniteGradedComplex.rank_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T04:00:01.28464+00:00
-- url     : https://prove2.me/submissions/4612c576-883c-4130-bbec-917ae3eaedfb

import Definitions.Def_SP4FiniteGradedComplex
import Mathlib.Tactic.Abel

set_option autoImplicit false
open scoped BigOperators
open SP4FiniteGradedComplex SP4GradedLaurent

private theorem degreewise {K : Type*} [Field K] {I : Type*} {C : I → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C) (i : I) :
    Module.finrank K (C (A.prev i)) = Module.finrank K (HomologyAtTarget A i) +
      blockRank A i + blockRank A (A.prev i) := by
  have hk : LinearMap.ker (incoming A i) = LinearMap.ker (A.d i) :=
    LinearMap.ker_codRestrict _ _ _
  have h₁ := LinearMap.finrank_range_add_finrank_ker (incoming A i)
  have h₂ := LinearMap.finrank_range_add_finrank_ker (A.d i)
  have h₃ := LinearMap.finrank_range_add_finrank_ker (A.d (A.prev i))
  have h₄ := (LinearMap.range (incoming A i)).finrank_quotient_add_finrank
  rw [hk] at h₁
  unfold HomologyAtTarget blockRank
  omega

private def kerPiEquiv {K : Type*} [Field K] {I : Type*} {C : I → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] (A : Data K I C) :
    LinearMap.ker (LinearMap.piMap A.d) ≃ₗ[K] (∀ i, LinearMap.ker (A.d i)) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => x i, funext (fun i => (x i).property)⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' k x := by rfl

private theorem total_ker {K : Type*} [Field K] {I : Type*} {C : I → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] (A : Data K I C) :
    LinearMap.ker (totalD A) = LinearMap.ker (LinearMap.piMap A.d) := by
  simp only [totalD, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

private theorem total_rank {K : Type*} [Field K] {I : Type*} [Fintype I]
    {C : I → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C) :
    Module.finrank K (LinearMap.range (totalD A)) = ∑ i, blockRank A i := by
  have hk : Module.finrank K (LinearMap.ker (totalD A)) =
      ∑ i, Module.finrank K (LinearMap.ker (A.d i)) := by
    rw [total_ker, (kerPiEquiv A).finrank_eq, Module.finrank_pi_fintype]
  have hr := LinearMap.finrank_range_add_finrank_ker (totalD A)
  rw [hk, Module.finrank_pi_fintype] at hr
  have hs : (∑ i, blockRank A i) + (∑ i, Module.finrank K (LinearMap.ker (A.d i))) =
      ∑ i, Module.finrank K (C i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact LinearMap.finrank_range_add_finrank_ker (A.d i)
  omega

private theorem total_coordinate {K : Type*} [Field K] {I : Type*} {C : I → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] (A : Data K I C)
    (x : ∀ i, C i) (i : I) : totalD A x (A.prev i) = A.d i (x i) := by
  have h := (LinearEquiv.piCongrLeft K C A.prev).symm_apply_apply
    (LinearMap.piMap A.d x)
  exact congrFun h i

private theorem total_square_zero {K : Type*} [Field K] {I : Type*} {C : I → Type*}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] (A : Data K I C) :
    (totalD A).comp (totalD A) = 0 := by
  ext x j
  obtain ⟨k, rfl⟩ := A.prev.surjective j
  obtain ⟨i, rfl⟩ := A.prev.surjective k
  change totalD A (totalD A x) (A.prev (A.prev i)) = 0
  rw [total_coordinate, total_coordinate]
  exact congrArg (fun f : C i →ₗ[K] C (A.prev (A.prev i)) => f (x i)) (A.square_zero i)

private theorem polynomial_identity {K : Type*} [Field K] {I : Type*} [Fintype I]
    {C : I → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C) :
    chainPolynomial A = homologyPolynomial A + tensorV (rankPolynomial A) := by
  classical
  have hshift (i : I) :
      Finsupp.single (A.degree (A.prev i)) (blockRank A i : ℤ) =
      Finsupp.mapDomain (fun m : ℤ => -1 + m)
        (Finsupp.single (A.degree i) (blockRank A i : ℤ)) := by
    by_cases hz : A.d i = 0
    · have hr : blockRank A i = 0 :=
        Submodule.finrank_eq_zero.mpr (LinearMap.range_eq_bot.mpr hz)
      simp [hr]
    · simp only [Finsupp.mapDomain_single, A.lowers_degree i hz]
      congr 1
      omega
  have hc : chainPolynomial A =
      ∑ i, Finsupp.single (A.degree (A.prev i)) (Module.finrank K (C (A.prev i)) : ℤ) := by
    exact (A.prev.sum_comp (fun i =>
      Finsupp.single (A.degree i) (Module.finrank K (C i) : ℤ))).symm
  have hparts : chainPolynomial A = homologyPolynomial A +
      (∑ i, Finsupp.single (A.degree (A.prev i)) (blockRank A i : ℤ)) +
      rankPolynomial A := by
    rw [hc]
    have hq : rankPolynomial A =
        ∑ i, Finsupp.single (A.degree (A.prev i)) (blockRank A (A.prev i) : ℤ) :=
      (A.prev.sum_comp (fun i => Finsupp.single (A.degree i) (blockRank A i : ℤ))).symm
    rw [hq, homologyPolynomial, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [degreewise A i]
    simp only [Nat.cast_add, Finsupp.single_add]
  have hs : (∑ i, Finsupp.single (A.degree (A.prev i)) (blockRank A i : ℤ)) =
      shift (-1) (rankPolynomial A) := by
    simp only [shift, rankPolynomial, Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl (fun i _ => hshift i)
  rw [hparts, hs, tensorV]
  abel

private theorem mass_single (m c : ℤ) : mass (Finsupp.single m c) = c := by
  change (Finsupp.single m c).sum (fun _ c => 1 * c) = c
  simp

private theorem mass_shift (k : ℤ) (P : GradedPolynomial) : mass (shift k P) = mass P := by
  change (Finsupp.mapDomain (fun m => k + m) P).sum (fun _ c => 1 * c) =
    P.sum (fun _ c => 1 * c)
  exact Finsupp.sum_mapDomain_index (by simp) (by intros; simp [mul_add])

private theorem mass_rank {K : Type*} [Field K] {I : Type*} [Fintype I]
    {C : I → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C) :
    mass (rankPolynomial A) = (Module.finrank K (LinearMap.range (totalD A)) : ℤ) := by
  rw [total_rank, rankPolynomial, map_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => mass_single _ _)

private theorem saturated {K : Type*} [Field K] {I : Type*} [Fintype I]
    {C : I → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C)
    (h : mass (chainPolynomial A) = mass (homologyPolynomial A)) :
    totalD A = 0 ∧ ∀ i, A.d i = 0 := by
  have hm := congrArg mass (polynomial_identity A)
  simp only [map_add, tensorV, mass_shift, mass_rank] at hm
  have hr : Module.finrank K (LinearMap.range (totalD A)) = 0 := by omega
  constructor
  · exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hr)
  · intro i
    have hs : (∑ j, blockRank A j) = 0 := (total_rank A).symm.trans hr
    have hi : blockRank A i ≤ ∑ j, blockRank A j :=
      Finset.single_le_sum (by intros; exact Nat.zero_le _) (Finset.mem_univ i)
    have hz : blockRank A i = 0 := by omega
    exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

theorem solution {K : Type*} [Field K] {I : Type*} [Fintype I]
    {C : I → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, FiniteDimensional K (C i)] (A : Data K I C) :
    (totalD A).comp (totalD A) = 0 ∧
    (∀ i, Module.finrank K (C (A.prev i)) = Module.finrank K (HomologyAtTarget A i) +
      blockRank A i + blockRank A (A.prev i)) ∧
    chainPolynomial A = homologyPolynomial A + tensorV (rankPolynomial A) ∧
    mass (rankPolynomial A) = (Module.finrank K (LinearMap.range (totalD A)) : ℤ) ∧
    (mass (chainPolynomial A) = mass (homologyPolynomial A) →
      totalD A = 0 ∧ ∀ i, A.d i = 0) := by
  exact ⟨total_square_zero A, degreewise A, polynomial_identity A, mass_rank A, saturated A⟩
