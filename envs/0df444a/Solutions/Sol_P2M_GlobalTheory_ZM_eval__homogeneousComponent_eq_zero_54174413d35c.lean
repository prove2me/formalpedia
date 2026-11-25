-- Prove2me | solution 1 for P2M_GlobalTheory_ZM_eval__homogeneousComponent_eq_zero_54174413d35c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:12.443845+00:00
-- url     : https://prove2.me/submissions/1a4a53e4-0428-4bf3-8b9d-814cb6f4b65f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapCompRingHomComp
import Theorems.Thm_P2M_GlobalTheory_ZM_coeff_eval__scale_d0dfcf2cdcc6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ)
    (h : MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_eval₂_scale β w F e]
  have key : Polynomial.toLaurent (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F) =
      MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
        (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F := by
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext i
      simp
  rw [h, ← map_zero Polynomial.toLaurent] at key
  rw [Polynomial.toLaurent_injective key, Polynomial.coeff_zero]
end GlobalTheory.ZM
