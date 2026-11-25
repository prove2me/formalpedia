-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isOpen_ballProd_34a603eb079e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:32.695314+00:00
-- url     : https://prove2.me/submissions/f694d9e4-9309-46f4-a693-5ba785e49fc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_hermNorm_group_3228c37461df

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (k : ℕ) : IsOpen (ballProd h k) := by
  have e : ballProd h k = ⋂ i, {u | h.norm (fun j => u (i, j)) < 1} := by
    ext u
    simp [ballProd]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_hermNorm_group h i) continuous_const
end GroundTheory.Heights₂.Heights
