-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_kappa_ne_zero_7c13c70c2d7e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:46.586353+00:00
-- url     : https://prove2.me/submissions/8abe317e-a48b-496c-a65a-ca78e2557c76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution {r a : ℕ} {κ : ℚ}
    (h : κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) : κ ≠ 0 := by
  have : ((r.factorial : ℚ) * a.factorial) ≠ 0 := by positivity
  rcases h with h | h <;> rw [h]
  · exact this
  · exact neg_ne_zero.mpr this
end GroundTheory.Heights₂.Heights.RestTerms.Top
