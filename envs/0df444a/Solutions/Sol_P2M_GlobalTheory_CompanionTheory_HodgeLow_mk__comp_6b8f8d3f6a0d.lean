-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_6b8f8d3f6a0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:52:35.860682+00:00
-- url     : https://prove2.me/submissions/8d6c8218-6167-4e08-85d8-5a3b5b10ee21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution (G : C' ⥤ C) (T : C') :
    ComposableArrows.mk₀ T ⋙ G = ComposableArrows.mk₀ (G.obj T) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i; rfl) (fun i hi ↦ by omega)
end GlobalTheory.CompanionTheory.HodgeLow
