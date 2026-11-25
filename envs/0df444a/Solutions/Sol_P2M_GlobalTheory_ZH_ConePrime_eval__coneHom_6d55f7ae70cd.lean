-- Prove2me | solution 1 for P2M_GlobalTheory_ZH_ConePrime_eval__coneHom_6d55f7ae70cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:08.346717+00:00
-- url     : https://prove2.me/submissions/0941da65-0fc1-4a21-98e2-b7595d41c245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k J A B : Type} [CommRing k] [CommRing A] [CommRing B]
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution (c : k →+* A) (r : J → A) (e : A →+* B) (t : B) (f : MvPolynomial J k) :
    Polynomial.eval₂ e t (coneHom c r f) = MvPolynomial.eval₂Hom (e.comp c) (fun j => e (r j) * t) f := by
  have : (Polynomial.eval₂RingHom e t).comp (coneHom c r) =
      MvPolynomial.eval₂Hom (e.comp c) (fun j => e (r j) * t) := by
    ext <;> simp [coneHom]
  exact RingHom.congr_fun this f
end GlobalTheory.ZH.ConePrime
