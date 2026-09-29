-- Prove2me | solution 1 for TensorProduct.mem_span_unitTmul_of_forall_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a2b5fad2-2cfc-5dfb-b358-8a33d5b3586a

import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero

set_option autoImplicit false
open scoped TensorProduct

noncomputable section

namespace UnitTensorDescent

open TensorProduct Function

variable {R S K T : Type}
  [CommRing R] [IsDomain R]
  [CommRing S] [Algebra R S]
  [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [AddCommGroup T] [Module R T]

theorem exists_smul_eq_one_tmul (z : FractionRing R ⊗[R] T) :
    ∃ (d : R) (y : T), d ≠ 0 ∧
      algebraMap R (FractionRing R) d • z = (1 : FractionRing R) ⊗ₜ[R] y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul c y =>
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
      refine ⟨(s : R), a • y, mem_nonZeroDivisors_iff_ne_zero.mp s.2, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, IsLocalization.mk'_spec',
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨d₁, y₁, hd₁, h₁⟩ := ih₁
      obtain ⟨d₂, y₂, hd₂, h₂⟩ := ih₂
      refine ⟨d₁ * d₂, d₂ • y₁ + d₁ • y₂, mul_ne_zero hd₁ hd₂, ?_⟩
      have e₁ : algebraMap R (FractionRing R) (d₁ * d₂) • z₁
          = algebraMap R (FractionRing R) d₂ • ((1 : FractionRing R) ⊗ₜ[R] y₁) := by
        rw [mul_comm d₁ d₂, map_mul, mul_smul, h₁]
      have e₂ : algebraMap R (FractionRing R) (d₁ * d₂) • z₂
          = algebraMap R (FractionRing R) d₁ • ((1 : FractionRing R) ⊗ₜ[R] y₂) := by
        rw [map_mul, mul_smul, h₂]
      rw [smul_add, e₁, e₂, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, smul_eq_mul, mul_one, mul_one, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
        ← TensorProduct.tmul_add]

theorem eq_zero_of_one_tmul_eq_zero [NoZeroSMulDivisors R T] {y : T}
    (h : (1 : FractionRing R) ⊗ₜ[R] y = 0) : y = 0 := by
  have h' : TensorProduct.mk R (FractionRing R) T 1 y = 0 := h
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R)
    (TensorProduct.mk R (FractionRing R) T 1)).mp h'
  rw [Submonoid.smul_def] at hs
  rcases smul_eq_zero.mp hs with h0 | h0
  · exact absurd h0 (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
  · exact h0

section WithFractionAlgebra

variable [Algebra (FractionRing R) K] [IsScalarTower R (FractionRing R) K]
variable [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K)]

def unitDecomp : K ⊗[FractionRing R] (FractionRing R ⊗[R] T) ≃ₗ[FractionRing R]
    (Module.Basis.ofVectorSpaceIndex (FractionRing R) K →₀ (FractionRing R ⊗[R] T)) :=
  (TensorProduct.congr (Module.Basis.ofVectorSpace (FractionRing R) K).repr
    (LinearEquiv.refl (FractionRing R) (FractionRing R ⊗[R] T))).trans
    (TensorProduct.finsuppScalarLeft (FractionRing R) (FractionRing R ⊗[R] T)
      (Module.Basis.ofVectorSpaceIndex (FractionRing R) K))

omit [Algebra R K] [IsScalarTower R (FractionRing R) K] in
theorem unitDecomp_tmul_apply (k : K) (z : FractionRing R ⊗[R] T)
    (j : Module.Basis.ofVectorSpaceIndex (FractionRing R) K) :
    unitDecomp (K := K) (T := T) (k ⊗ₜ[FractionRing R] z) j
      = (Module.Basis.ofVectorSpace (FractionRing R) K).repr k j • z := by
  simp [unitDecomp, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TensorProduct.finsuppScalarLeft_apply_tmul_apply]

omit [Algebra R K] [IsScalarTower R (FractionRing R) K] in
theorem unitDecomp_symm_single (j : Module.Basis.ofVectorSpaceIndex (FractionRing R) K)
    (z : FractionRing R ⊗[R] T) :
    (unitDecomp (K := K) (T := T)).symm (Finsupp.single j z)
      = ((Module.Basis.ofVectorSpace (FractionRing R) K) j : K) ⊗ₜ[FractionRing R] z := by
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext fun i => ?_
  rw [unitDecomp_tmul_apply, Module.Basis.repr_self, Finsupp.single_apply,
    Finsupp.single_apply]
  split_ifs with h
  · rw [one_smul]
  · rw [zero_smul]

omit [Algebra R K] [IsScalarTower R (FractionRing R) K] in

theorem unitDecomp_lTensor_apply (h : T →ₗ[R] T)
    (u : K ⊗[FractionRing R] (FractionRing R ⊗[R] T))
    (j : Module.Basis.ofVectorSpaceIndex (FractionRing R) K) :
    unitDecomp (K := K) (T := T)
        (LinearMap.lTensor K (h.baseChange (FractionRing R)) u) j
      = h.baseChange (FractionRing R) (unitDecomp (K := K) (T := T) u j) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k z => rw [LinearMap.lTensor_tmul, unitDecomp_tmul_apply, unitDecomp_tmul_apply,
      map_smul]
  | add u₁ u₂ ih₁ ih₂ => rw [map_add, map_add, Finsupp.add_apply, ih₁, ih₂, map_add,
      Finsupp.add_apply, map_add]

omit [Algebra R K] [IsScalarTower R (FractionRing R) K] in

theorem eq_sum_unitDecomp (u : K ⊗[FractionRing R] (FractionRing R ⊗[R] T)) :
    u = (unitDecomp (K := K) (T := T) u).sum fun j z =>
      ((Module.Basis.ofVectorSpace (FractionRing R) K) j : K) ⊗ₜ[FractionRing R] z := by
  conv_lhs => rw [← LinearEquiv.symm_apply_apply (unitDecomp (K := K) (T := T)) u,
    ← Finsupp.sum_single (unitDecomp (K := K) (T := T) u)]
  rw [map_finsuppSum]
  exact Finsupp.sum_congr fun j _ => unitDecomp_symm_single j _

omit [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K)] [IsDomain R] in

theorem baseChange_cancelBaseChange (h : T →ₗ[R] T)
    (u : K ⊗[FractionRing R] (FractionRing R ⊗[R] T)) :
    h.baseChange K (AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T u)
      = AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T
          (LinearMap.lTensor K (h.baseChange (FractionRing R)) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c y => simp
      | add z₁ z₂ ih₁ ih₂ => rw [TensorProduct.tmul_add, map_add, map_add, ih₁, ih₂,
          map_add, map_add]
  | add u₁ u₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

omit [DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K)] in

theorem mem_span_one_tmul_of_forall_baseChange_eq_zero [NoZeroSMulDivisors R T]
    {ι : Type} (f : ι → T →ₗ[R] T) (w : K ⊗[R] T)
    (hw : ∀ i, (f i).baseChange K w = 0) :
    w ∈ Submodule.span K
      {z : K ⊗[R] T | ∃ y : T, (∀ i, f i y = 0) ∧ z = (1 : K) ⊗ₜ[R] y} := by
  classical
  haveI : DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K) :=
    Classical.decEq _
  have hker : ∀ i, LinearMap.lTensor K ((f i).baseChange (FractionRing R))
      ((AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T).symm w) = 0 := by
    intro i
    apply (AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T).injective
    rw [← baseChange_cancelBaseChange, LinearEquiv.apply_symm_apply, hw i, map_zero]
  have hwu : w = AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T
      ((AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T).symm w) :=
    (LinearEquiv.apply_symm_apply _ _).symm
  generalize hu : (AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T).symm w
    = u at hker hwu
  have hcomp : ∀ (j : Module.Basis.ofVectorSpaceIndex (FractionRing R) K) (i : ι),
      (f i).baseChange (FractionRing R) (unitDecomp (K := K) (T := T) u j) = 0 := by
    intro j i
    rw [← unitDecomp_lTensor_apply, hker i, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hterm : ∀ j : Module.Basis.ofVectorSpaceIndex (FractionRing R) K,
      AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T
        (((Module.Basis.ofVectorSpace (FractionRing R) K) j : K) ⊗ₜ[FractionRing R]
          unitDecomp (K := K) (T := T) u j)
      ∈ Submodule.span K
        {z : K ⊗[R] T | ∃ y : T, (∀ i, f i y = 0) ∧ z = (1 : K) ⊗ₜ[R] y} := by
    intro j
    obtain ⟨d, y, hd, hdz⟩ := exists_smul_eq_one_tmul (unitDecomp (K := K) (T := T) u j)
    have hy : ∀ i, f i y = 0 := by
      intro i
      apply eq_zero_of_one_tmul_eq_zero (R := R)
      have h1 : (f i).baseChange (FractionRing R) ((1 : FractionRing R) ⊗ₜ[R] y) = 0 := by
        rw [← hdz, map_smul, hcomp j i, smul_zero]
      rwa [LinearMap.baseChange_tmul] at h1
    have halg : algebraMap R (FractionRing R) d ≠ 0 := fun h0 =>
      hd (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
    have hzj : unitDecomp (K := K) (T := T) u j
        = (algebraMap R (FractionRing R) d)⁻¹ • ((1 : FractionRing R) ⊗ₜ[R] y) := by
      rw [← hdz, inv_smul_smul₀ halg]
    rw [hzj, ← TensorProduct.smul_tmul, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    have hsm : ((algebraMap R (FractionRing R) d)⁻¹ •
          ((Module.Basis.ofVectorSpace (FractionRing R) K) j : K)) ⊗ₜ[R] y
        = ((algebraMap R (FractionRing R) d)⁻¹ •
            ((Module.Basis.ofVectorSpace (FractionRing R) K) j : K)) •
          ((1 : K) ⊗ₜ[R] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  rw [hwu, eq_sum_unitDecomp u, map_finsuppSum]
  exact Submodule.finsuppSum_mem K _ _ _ fun j _ => hterm j

end WithFractionAlgebra

omit [IsDomain R] in

theorem one_tmul_one_tmul_smul (c : R) (x : T) :
    (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (c • x))
      = algebraMap R K c • ((1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) := by
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, algebraMap_smul]

section WithFractionAlgebra

variable [Algebra (FractionRing R) K] [IsScalarTower R (FractionRing R) K]

theorem eq_zero_of_one_tmul_one_tmul_eq_zero [NoZeroSMulDivisors R T] {x : T}
    (h : (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) = 0) : x = 0 := by
  classical
  haveI : DecidableEq ↑(Module.Basis.ofVectorSpaceIndex (FractionRing R) K) :=
    Classical.decEq _
  have h1 : (1 : K) ⊗ₜ[R] x = 0 := by
    have h0 := congrArg (AlgebraTensorModule.cancelBaseChange R S K K T) h
    rwa [AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] at h0
  have h2 : (1 : K) ⊗ₜ[FractionRing R] ((1 : FractionRing R) ⊗ₜ[R] x) = 0 := by
    have h0 := congrArg
      (AlgebraTensorModule.cancelBaseChange R (FractionRing R) K K T).symm h1
    rwa [AlgebraTensorModule.cancelBaseChange_symm_tmul, map_zero] at h0
  have h3 : ∀ j, unitDecomp (K := K) (T := T)
      ((1 : K) ⊗ₜ[FractionRing R] ((1 : FractionRing R) ⊗ₜ[R] x)) j = 0 := by
    intro j
    rw [h2, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h4 : ∃ j, (Module.Basis.ofVectorSpace (FractionRing R) K).repr 1 j ≠ 0 := by
    by_contra hno
    have hall : ∀ j, (Module.Basis.ofVectorSpace (FractionRing R) K).repr 1 j = 0 :=
      fun j => not_not.mp fun h => hno ⟨j, h⟩
    exact one_ne_zero
      ((Module.Basis.ofVectorSpace (FractionRing R) K).repr.map_eq_zero_iff.mp
        (Finsupp.ext hall))
  obtain ⟨j, hj⟩ := h4
  have h5 := h3 j
  rw [unitDecomp_tmul_apply] at h5
  have h6 : (1 : FractionRing R) ⊗ₜ[R] x = 0 := by
    have := congrArg (fun z => ((Module.Basis.ofVectorSpace (FractionRing R) K).repr 1 j)⁻¹ • z) h5
    simpa [inv_smul_smul₀ hj] using this
  exact eq_zero_of_one_tmul_eq_zero h6

theorem eq_of_one_tmul_one_tmul_eq [NoZeroSMulDivisors R T] {x x' : T}
    (h : (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) = (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x')) : x = x' := by
  have h0 : (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (x - x')) = 0 := by
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_sub, h, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_one_tmul_one_tmul_eq_zero h0)

end WithFractionAlgebra

theorem mem_span_unitTmul_of_forall_apply_eq_zero [NoZeroSMulDivisors R T]
    (hinj : Function.Injective (algebraMap R K))
    {ι : Type} (Φ : ι → (K ⊗[S] (S ⊗[R] T)) →ₗ[K] (K ⊗[S] (S ⊗[R] T))) (g : ι → T → T)
    (hcomm : ∀ (i : ι) (k : K) (x : T),
      Φ i (k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) = k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] g i x))
    (v : K ⊗[S] (S ⊗[R] T)) (hv : ∀ i, Φ i v = 0) :
    v ∈ Submodule.span K
      {z : K ⊗[S] (S ⊗[R] T) | ∃ y : T, (∀ i, g i y = 0) ∧
        z = (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)} := by
  letI : Algebra (FractionRing R) K := RingHom.toAlgebra (IsFractionRing.lift hinj)
  haveI : IsScalarTower R (FractionRing R) K := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun x => (IsFractionRing.lift_algebraMap hinj x).symm)

  have hadd : ∀ i (x x' : T), g i (x + x') = g i x + g i x' := by
    intro i x x'
    apply eq_of_one_tmul_one_tmul_eq (R := R) (S := S) (K := K)
    rw [← hcomm i 1 (x + x'), TensorProduct.tmul_add (1 : S), TensorProduct.tmul_add (1 : K),
      map_add, hcomm i 1 x, hcomm i 1 x', TensorProduct.tmul_add (1 : S),
      TensorProduct.tmul_add (1 : K)]
  have hsmul : ∀ i (c : R) (x : T), g i (c • x) = c • g i x := by
    intro i c x
    apply eq_of_one_tmul_one_tmul_eq (R := R) (S := S) (K := K)
    rw [← hcomm i 1 (c • x), one_tmul_one_tmul_smul, map_smul, hcomm i 1 x,
      ← one_tmul_one_tmul_smul]
  let f : ι → T →ₗ[R] T := fun i =>
    { toFun := g i
      map_add' := hadd i
      map_smul' := hsmul i }

  have hconj : ∀ i (u : K ⊗[S] (S ⊗[R] T)),
      AlgebraTensorModule.cancelBaseChange R S K K T (Φ i u)
        = (f i).baseChange K (AlgebraTensorModule.cancelBaseChange R S K K T u) := by
    intro i u
    induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul k m =>
        induction m using TensorProduct.induction_on with
        | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
        | tmul s x =>
            have hrw : k ⊗ₜ[S] (s ⊗ₜ[R] x) = (s • k) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) := by
              rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [hrw, hcomm i (s • k) x]
            simp only [AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
              LinearMap.baseChange_tmul]
            rfl
        | add m₁ m₂ ih₁ ih₂ =>
            rw [TensorProduct.tmul_add, map_add, map_add, ih₁, ih₂, map_add, map_add]
    | add u₁ u₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]
  have hv' : ∀ i, (f i).baseChange K (AlgebraTensorModule.cancelBaseChange R S K K T v) = 0 := by
    intro i
    rw [← hconj i v, hv i, map_zero]
  have hmem := mem_span_one_tmul_of_forall_baseChange_eq_zero f
    (AlgebraTensorModule.cancelBaseChange R S K K T v) hv'
  have hmap : (AlgebraTensorModule.cancelBaseChange R S K K T).symm
      (AlgebraTensorModule.cancelBaseChange R S K K T v)
      ∈ Submodule.map
        ((AlgebraTensorModule.cancelBaseChange R S K K T).symm :
          K ⊗[R] T ≃ₗ[K] K ⊗[S] (S ⊗[R] T)).toLinearMap
        (Submodule.span K {z : K ⊗[R] T | ∃ y : T, (∀ i, f i y = 0) ∧ z = (1 : K) ⊗ₜ[R] y}) :=
    Submodule.mem_map_of_mem hmem
  rw [LinearEquiv.symm_apply_apply, Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨y, hy, ?_⟩
  rw [LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul]

end UnitTensorDescent

end

theorem solution
    {R S K T : Type}
    [CommRing R]
    [CommRing S] [Algebra R S]
    [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [AddCommGroup T] [Module R T] [NoZeroSMulDivisors R T]
    (hinj : Function.Injective (algebraMap R K))
    {ι : Type} (Φ : ι → (K ⊗[S] (S ⊗[R] T)) →ₗ[K] (K ⊗[S] (S ⊗[R] T))) (g : ι → T → T)
    (hcomm : ∀ (i : ι) (k : K) (x : T),
      Φ i (k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) = k ⊗ₜ[S] ((1 : S) ⊗ₜ[R] g i x))
    (v : K ⊗[S] (S ⊗[R] T)) (hv : ∀ i, Φ i v = 0) :
    v ∈ Submodule.span K
      {z : K ⊗[S] (S ⊗[R] T) | ∃ y : T, (∀ i, g i y = 0) ∧
        z = (1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y)} :=
  haveI : IsDomain R := Function.Injective.isDomain _ hinj
  UnitTensorDescent.mem_span_unitTmul_of_forall_apply_eq_zero hinj Φ g hcomm v hv

#print axioms solution

end S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero
end P2MW
export P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero (solution)
