-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hodge_WedgeField_sqEquiv__Multi_7d7f7aa32a02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:52:41.15579+00:00
-- url     : https://prove2.me/submissions/4e222fa9-1132-4fdb-8793-fbe2db84eeb6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.WedgeField
namespace GlobalTheory.CompanionTheory.Hodge.WedgeField
theorem _root_.solution {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl
end GlobalTheory.CompanionTheory.Hodge.WedgeField
