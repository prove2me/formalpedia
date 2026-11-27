-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_evalCone_one_blockForms_63740f3013e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:38.943911+00:00
-- url     : https://prove2.me/submissions/1221d4f3-4654-4711-a9be-9c9249019482

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (j : Fin ((blockAddData n k₀).size + 1)) :
    evalCone (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) (blockForms n k₀ c j) ≠ 0 := by
  simp [evalCone, blockForms, chartMonomial]
end GroundTheory.Heights₂.Heights
