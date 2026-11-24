-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:49.488063+00:00
-- url     : https://prove2.me/submissions/6b42a6f8-c9e6-4bcc-901a-0d8659223d7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open Finset
open GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
namespace GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  calc Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) (by linarith)
    _ = 2 * (Real.log p / p) := by ring
end GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum
