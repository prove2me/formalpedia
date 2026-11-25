-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_chartCoord_989f89da8026
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:09.971039+00:00
-- url     : https://prove2.me/submissions/cdcffd6c-d290-4a87-bf35-6936b4327794

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
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
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (v : Coord n) :
    funHom P y hP (P.chartCoord c v) = constMap ι (y v / y ⟨v.1, c v.1⟩) := by
  rw [ArithVariety.chartCoord, map_div₀, funHom_mkF, funHom_mkF, coneHom_X, coneHom_X, map_div₀,
    mul_div_mul_right _ _ (varT_ne_zero v.1)]
end GroundTheory.Heights₂.Heights.AddBlockBridge
