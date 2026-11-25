-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_antisymSample_eq_6e77b6491340
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:08.73309+00:00
-- url     : https://prove2.me/submissions/9b07dc60-0a47-4580-ad73-359e34063b86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymDelta_fin_one_three_8a2ce2972f0c

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : antisymSample =
    (X (0, 0) - X (0, 1)) * (X (0, 0) - X (0, 2)) * (X (0, 1) - X (0, 2)) *
      (X (0, 0) + X (0, 1) + X (0, 2)) := by
  rw [antisymSample, antisymDelta_fin_one_three, Fintype.sum_prod_type, Fin.sum_univ_one,
    Fin.sum_univ_three]
end GroundTheory.Heights₂.Heights
