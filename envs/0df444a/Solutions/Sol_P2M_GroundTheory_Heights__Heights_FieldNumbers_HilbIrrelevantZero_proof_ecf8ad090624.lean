-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbIrrelevantZero_proof_ecf8ad090624
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:24.244087+00:00
-- url     : https://prove2.me/submissions/d876a94e-1689-45ce-a7e7-b0fba31f68e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbIrrelevantZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_bot_of_not_isRelevant_05c8187c8ccb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace HilbIrrelevantZero
theorem _root_.solution : HilbIrrelevantZero.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
  have hpos : ∀ k, 0 ≤ m k := fun k => le_trans zero_le_one (hm k)
  unfold hilbFn
  rw [if_pos hpos, gradedPiece_eq_bot_of_not_isRelevant hI (m := fun k => (m k).toNat)]
  · simp
  · intro k
    have := hm k
    simp only [Pi.one_apply] at this
    omega
end HilbIrrelevantZero
end GroundTheory.Heights₂.Heights.FieldNumbers
