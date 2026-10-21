-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.bilinear_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:29:18.183726+00:00
-- url     : https://prove2.me/submissions/edd20884-9545-4b1b-b2b6-058eca078cd7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04
noncomputable section

set_option synthInstance.maxSize 8192

open QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]


theorem g66r_dense : DenseRange (algebraicInclusion (K := K) (X := X) (Y := Y)) := by
  have h1 : DenseRange (fun u : NormedAlgebraic K X Y => (u : Projective K X Y)) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : DenseRange (SeparationQuotient.mk : Algebraic K X Y → NormedAlgebraic K X Y) :=
    SeparationQuotient.surjective_mk.denseRange
  exact h1.comp h2 (UniformSpace.Completion.continuous_coe _)

theorem g66r_unif : IsUniformInducing (algebraicInclusion (K := K) (X := X) (Y := Y)) := by
  have h1 : IsUniformInducing (fun u : NormedAlgebraic K X Y => (u : Projective K X Y)) :=
    UniformSpace.Completion.isUniformInducing_coe _
  have h2 : IsUniformInducing (SeparationQuotient.mk : Algebraic K X Y → NormedAlgebraic K X Y) :=
    SeparationQuotient.isUniformInducing_mk
  exact h1.comp h2

theorem g66r_norm (u : Algebraic K X Y) : ‖algebraicInclusion (K := K) (X := X) (Y := Y) u‖ = ‖u‖ := by
  show ‖((SeparationQuotient.mk u : NormedAlgebraic K X Y) : Projective K X Y)‖ = ‖u‖
  rw [UniformSpace.Completion.norm_coe, SeparationQuotient.norm_mk]

theorem g66r_ext_eq (B : Bilinear K X Y Z) (u : Algebraic K X Y) :
    extendBilinear B (algebraicInclusion u) = PiTensorProduct.liftIsometry K (Factors X Y) Z B u :=
  ContinuousLinearMap.extend_eq _ g66r_dense g66r_unif u

theorem g66r_ext_tprod (B : Bilinear K X Y Z) (m : (b : Bool) → Factors X Y b) :
    extendBilinear B (algebraicInclusion (PiTensorProduct.tprod K m)) = B m := by
  rw [g66r_ext_eq, PiTensorProduct.liftIsometry_apply_apply, PiTensorProduct.lift.tprod]
  rfl

theorem g66r_ext_pure (B : Bilinear K X Y Z) (x : X) (y : Y) :
    extendBilinear B (pure x y) = B (pair x y) :=
  g66r_ext_tprod B (pair x y)

theorem g66r_uniq (L1 L2 : Projective K X Y →L[K] Z) (h : ∀ x y, L1 (pure x y) = L2 (pure x y)) :
    L1 = L2 := by
  have hc : L1.comp algebraicInclusion = L2.comp algebraicInclusion := by
    apply ContinuousLinearMap.coe_injective
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    have hm : m = pair (m false).down (m true).down := by
      funext b; cases b <;> rfl
    rw [hm]
    exact h _ _
  rw [← ContinuousLinearMap.extend_unique (L1.comp algebraicInclusion) g66r_dense g66r_unif L1 rfl,
    ← ContinuousLinearMap.extend_unique (L2.comp algebraicInclusion) g66r_dense g66r_unif L2 rfl, hc]

theorem g66r_ext_norm (B : Bilinear K X Y Z) : ‖extendBilinear B‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  refine g66r_dense.induction_on z (isClosed_le (by fun_prop) (by fun_prop)) fun u => ?_
  rw [g66r_ext_eq, g66r_norm]
  calc ‖PiTensorProduct.liftIsometry K (Factors X Y) Z B u‖
      ≤ ‖PiTensorProduct.liftIsometry K (Factors X Y) Z B‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖B‖ * ‖u‖ := by rw [LinearIsometryEquiv.norm_map]

theorem g66r_incl_norm : ‖algebraicInclusion (K := K) (X := X) (Y := Y)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by rw [g66r_norm, one_mul]

theorem g66r_res_norm (L : Projective K X Y →L[K] Z) : ‖restrictBilinear L‖ ≤ ‖L‖ := by
  have : restrictBilinear L = (PiTensorProduct.liftIsometry K (Factors X Y) Z).symm
      (L.comp algebraicInclusion) := rfl
  rw [this, LinearIsometryEquiv.norm_map]
  calc ‖L.comp algebraicInclusion‖ ≤ ‖L‖ * ‖algebraicInclusion (K := K) (X := X) (Y := Y)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * 1 := by gcongr; exact g66r_incl_norm
    _ = ‖L‖ := mul_one _

/-- PDF pp.3–4, §2.2: actual canonical extension/restriction maps form an isometry;
continuous extensions are unique, and absolutely summable series are evaluated termwise. -/
theorem solution [CompleteSpace X] [CompleteSpace Y] :
    (∃ E : Bilinear K X Y Z ≃ₗᵢ[K] (Projective K X Y →L[K] Z),
      (∀ B, E B = extendBilinear B) ∧ (∀ L, E.symm L = restrictBilinear L)) ∧
    (∀ (B : Bilinear K X Y Z) x y, extendBilinear B (pure x y) = B (pair x y)) ∧
    (∀ (B : Bilinear K X Y Z) (L : Projective K X Y →L[K] Z),
      (∀ x y, L (pure x y) = B (pair x y)) → L = extendBilinear B) ∧
    (∀ (B : Bilinear K X Y Z) z x y, TensorRep z x y →
      HasSum (fun n => B (pair (x n) (y n))) (extendBilinear B z)) := by
  have hadd : ∀ B B' : Bilinear K X Y Z, extendBilinear (B + B') = extendBilinear B + extendBilinear B' := by
    intro B B'
    apply g66r_uniq
    intro x y
    simp only [ContinuousLinearMap.add_apply, g66r_ext_pure, ContinuousMultilinearMap.add_apply]
  have hsmul : ∀ (r : K) (B : Bilinear K X Y Z), extendBilinear (r • B) = r • extendBilinear B := by
    intro r B
    apply g66r_uniq
    intro x y
    simp only [ContinuousLinearMap.smul_apply, g66r_ext_pure, ContinuousMultilinearMap.smul_apply]
  have hleft : ∀ B : Bilinear K X Y Z, restrictBilinear (extendBilinear B) = B := by
    intro B
    ext m
    show extendBilinear B (algebraicInclusion (PiTensorProduct.tprodL K m)) = B m
    rw [PiTensorProduct.tprodL_toFun]
    exact g66r_ext_tprod B m
  have hright : ∀ L : Projective K X Y →L[K] Z, extendBilinear (restrictBilinear L) = L := by
    intro L
    apply g66r_uniq
    intro x y
    rw [g66r_ext_pure]
    show L (algebraicInclusion (PiTensorProduct.tprodL K (pair x y))) = L (pure x y)
    rw [PiTensorProduct.tprodL_toFun]
    rfl
  let e : Bilinear K X Y Z ≃ₗ[K] (Projective K X Y →L[K] Z) :=
    { toFun := extendBilinear
      map_add' := hadd
      map_smul' := hsmul
      invFun := restrictBilinear
      left_inv := hleft
      right_inv := hright }
  refine ⟨⟨LinearIsometryEquiv.ofBounds e g66r_ext_norm g66r_res_norm, fun B => rfl, fun L => rfl⟩,
    g66r_ext_pure, ?_, ?_⟩
  · intro B L h
    apply g66r_uniq
    intro x y
    rw [h, g66r_ext_pure]
  · intro B z x y hrep
    have := (extendBilinear B).hasSum hrep.2.2
    simpa only [g66r_ext_pure] using this

end Banach


end
