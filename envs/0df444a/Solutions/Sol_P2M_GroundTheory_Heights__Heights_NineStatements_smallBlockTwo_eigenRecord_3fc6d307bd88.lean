-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_eigenRecord_3fc6d307bd88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:11.989883+00:00
-- url     : https://prove2.me/submissions/707d45f5-4411-4038-bd3c-c2547bcbb4c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
    (ι : E →+* L) {j' : ℕ} (hj : 1 ≤ j') : EigenRecordAt (fun _ => ι) j' (smallBlockTwo ι) := by
  intro τ 𝔓
  have h0 := FractionalIdeal.count_coe_nonneg L 𝔓 (extDifferent ι)
  simp only [smallBlockTwo, one_mul]
  rw [FractionalIdeal.count_inv, Int.cast_neg, abs_neg, abs_of_nonneg (by exact_mod_cast h0)]
  exact le_mul_of_one_le_left (by exact_mod_cast h0) (by exact_mod_cast hj)
end GroundTheory.Heights₂.Heights.NineStatements
