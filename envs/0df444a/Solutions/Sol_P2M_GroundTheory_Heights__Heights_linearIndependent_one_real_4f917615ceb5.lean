-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearIndependent_one_real_4f917615ceb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:10:59.894887+00:00
-- url     : https://prove2.me/submissions/7bccdb3e-9801-4c25-b816-13791a304211

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
theorem _root_.solution : LinearIndependent ℝ ![(1 : ℝ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  simpa using hg
end GroundTheory.Heights₂.Heights
