-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:34.762818+00:00
-- url     : https://prove2.me/submissions/95256983-563c-4217-8da5-01874ce4b147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f

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
theorem _root_.solution (L : Type) [Field L] [NumberField L] {q : ℕ} (hq : q.Prime) : primeFrac L q ≠ 0 := by
  rw [primeFrac, Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact primeSpan_ne_bot hq
end GroundTheory.Heights₂.Heights.NineStatements
