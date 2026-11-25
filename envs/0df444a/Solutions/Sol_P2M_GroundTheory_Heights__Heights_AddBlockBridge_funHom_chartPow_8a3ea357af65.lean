-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartPow_8a3ea357af65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:12.690053+00:00
-- url     : https://prove2.me/submissions/ca5914f2-6ca2-42d1-a4b3-8d2150efd546

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    funHom P y hP (P.chartPow c a) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k) * ∏ k, varT k ^ a k := by
  rw [ArithVariety.chartPow, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_zpow₀, funHom_mkF, coneHom_X, mul_zpow]
end GroundTheory.Heights₂.Heights.AddBlockBridge
