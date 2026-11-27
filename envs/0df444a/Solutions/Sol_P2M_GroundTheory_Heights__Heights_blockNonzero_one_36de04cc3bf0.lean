-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockNonzero_one_36de04cc3bf0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:54.297408+00:00
-- url     : https://prove2.me/submissions/41eee9a5-9f4c-4846-8f0f-0e591b83e3e6

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : BlockNonzero (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) :=
  fun _ h ↦ one_ne_zero (congrFun h 0)
end GroundTheory.Heights₂.Heights
