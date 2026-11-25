-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isLive_21de13e30d11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:19.958459+00:00
-- url     : https://prove2.me/submissions/01d49cd3-083d-4cda-ae53-eccbca542418

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
open GroundTheory.Heights₂.Heights.ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) : (whole n).IsLive c := fun _ h ↦
  X_ne_zero _ ((Submodule.mem_bot _).mp h)
end GroundTheory.Heights₂.Heights.ArithVariety
