-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:46.835746+00:00
-- url     : https://prove2.me/submissions/b4b129b3-ec9e-43a3-b4da-17f4da9bd4a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (U : X.Opens) (hU : IsAffineOpen U) (a : Γ(X, U)) (s : S) :
    letI := (algX p U).toAlgebra
    eTens p p' φ H U hU (a ⊗ₜ[R] s) = (φ.appLE U _ inf_le_left).hom a * algX p' _ s := by
  letI := (algX p U).toAlgebra
  have h1 := congrArg (fun q => q.hom a)
    (IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R Γ(X, U) S)
      (isPushout_sections p p' φ H U hU))
  have h2 := congrArg (fun q => q.hom s)
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R Γ(X, U) S)
      (isPushout_sections p p' φ H U hU))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  have e : a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * ((1 : Γ(X, U)) ⊗ₜ[R] s) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e, map_mul]
  exact congrArg₂ (· * ·) h1 h2
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
