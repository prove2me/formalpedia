-- Prove2me | solution 1 for P2M_GlobalTheory_AbCoh_TwoFormSum__Multi_two_bb841c234bcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:07.622605+00:00
-- url     : https://prove2.me/submissions/0bf54a5e-5142-4d2e-896c-6cfee52f268e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.TwoFormSum
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
namespace GlobalTheory.AbCoh.TwoFormSum
theorem _root_.solution (v : Fin 2 → Ω[B⁄R]) : exteriorPower.ιMulti B 2 v = wedge R B (v 0) (v 1) := by
  rw [wedge_eq_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl
end GlobalTheory.AbCoh.TwoFormSum
