-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HodgeTwoForm_nu__Multi_5c9fdc71b212
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:05.611808+00:00
-- url     : https://prove2.me/submissions/f888379b-a8be-4aaa-8860-64c2d8752083

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (a b : Glob1 F) (T : C) :
    nu F (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T) := by
  rw [wedge_eq_ιMulti]
  change exteriorPower.alternatingMapLinearEquiv (wedgeAt F T) _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change exteriorPower.ιMulti (F.obj T) 2 (fun i ↦ evForm F T (![a, b] i)) = _
  congr 1
  ext i; fin_cases i <;> rfl
end GlobalTheory.CompanionTheory.HodgeTwoForm
