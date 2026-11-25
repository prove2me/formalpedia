-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:26.351946+00:00
-- url     : https://prove2.me/submissions/9e2353cf-06de-4759-8fc7-272344bc88e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_eTens_tmul

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
theorem _root_.solution (U : X.Opens) (hU : IsAffineOpen U) (u : Γ(X, U))
    (x : letI := (algX p U).toAlgebra; Γ(X, U) ⊗[R] S) :
    letI := (algX p U).toAlgebra
    eTens p p' φ H U hU ((mulL p U u).rTensor S x) = (φ.appLE U _ inf_le_left).hom u * eTens p p' φ H U hU x := by
  letI := (algX p U).toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, (eTens p p' φ H U hU).map_zero, mul_zero]
  | tmul a s =>
    rw [LinearMap.rTensor_tmul, eTens_tmul, eTens_tmul]
    show (φ.appLE U _ _).hom (u * a) * _ = _
    rw [map_mul]; ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
