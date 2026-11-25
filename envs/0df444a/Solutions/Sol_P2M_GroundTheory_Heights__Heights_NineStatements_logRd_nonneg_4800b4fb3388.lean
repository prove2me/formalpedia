-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_logRd_nonneg_4800b4fb3388
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:47.04868+00:00
-- url     : https://prove2.me/submissions/d8f51fa3-6bd6-4e3b-a7b2-6cc36426a89b

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] : 0 ≤ logRd E := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Real.log_nonneg
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  exact_mod_cast h
end GroundTheory.Heights₂.Heights.NineStatements
