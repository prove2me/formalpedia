-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratIntegerBasis_apply_239c16315f02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:52.416056+00:00
-- url     : https://prove2.me/submissions/f07c085d-5051-4970-8f22-1fffdcd9bd44

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
theorem _root_.solution (a : Fin (0 + 1)) : ((ratIntegerBasis a : 𝓞 ℚ) : ℚ) = 1 := by
  simp [ratIntegerBasis, Module.Basis.singleton_apply]
end GroundTheory.Heights₂.Heights
