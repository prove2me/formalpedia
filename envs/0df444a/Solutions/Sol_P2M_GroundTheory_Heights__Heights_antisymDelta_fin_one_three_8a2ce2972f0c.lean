-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_antisymDelta_fin_one_three_8a2ce2972f0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:53.920198+00:00
-- url     : https://prove2.me/submissions/c0e06d17-5159-428d-a0a7-d12ca1a1e892

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Ioi_zero_fin_three_6422cebaa51c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Ioi_one_fin_three_5b56014662a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Ioi_two_fin_three_d77186bce237

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
theorem _root_.solution :
    antisymDelta (Fin 1) 3 = (X (0, 0) - X (0, 1)) * (X (0, 0) - X (0, 2)) * (X (0, 1) - X (0, 2)) := by
  rw [antisymDelta, Fin.prod_univ_one, Fin.prod_univ_three, Ioi_zero_fin_three, Ioi_one_fin_three, Ioi_two_fin_three]
  simp only [Finset.prod_pair (show (1 : Fin 3) ≠ 2 by decide), Finset.prod_singleton,
    Finset.prod_empty]
  ring
end GroundTheory.Heights₂.Heights
