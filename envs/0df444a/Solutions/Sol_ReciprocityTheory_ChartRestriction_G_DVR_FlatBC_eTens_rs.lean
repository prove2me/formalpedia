-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:33.517295+00:00
-- url     : https://prove2.me/submissions/c81b843d-b055-4acb-957d-b3108e21bfc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_eTens_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul


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
theorem _root_.solution (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U)
    (x : letI := (algX p U).toAlgebra; Γ(X, U) ⊗[R] S) :
    letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
    eTens p p' φ H U' hU' ((rsL p U U' h).rTensor S x) =
      ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_inf (Scheme.Hom.preimage_mono φ h) le_rfl) (eTens p p' φ H U hU x) := by
  letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, (eTens p p' φ H U' hU').map_zero, (eTens p p' φ H U hU).map_zero]
    exact (map_zero _).symm
  | tmul a s =>
    rw [LinearMap.rTensor_tmul, eTens_tmul, eTens_tmul, ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX]
    congr 1
    show (φ.appLE U' _ _).hom (ReciprocityTheory.ChartRestriction.G.DVR.rs h a) = ReciprocityTheory.ChartRestriction.G.DVR.rs _ ((φ.appLE U _ _).hom a)
    simp only [ReciprocityTheory.ChartRestriction.G.DVR.rs]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  | add x y hx hy => simp only [map_add, hx, hy]
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
