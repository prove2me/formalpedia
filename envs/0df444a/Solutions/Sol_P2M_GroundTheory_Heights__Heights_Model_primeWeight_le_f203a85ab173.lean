-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_primeWeight_le_f203a85ab173
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:06:01.3574+00:00
-- url     : https://prove2.me/submissions/69f557e1-0314-4e64-a6f2-ea81b846ef04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSumCp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {p : ℕ} (hp : p.Prime) : primeWeight p ≤ 4 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeWeight
  split_ifs with h
  · subst h; norm_num
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
end GroundTheory.Heights₂.Heights.Model
