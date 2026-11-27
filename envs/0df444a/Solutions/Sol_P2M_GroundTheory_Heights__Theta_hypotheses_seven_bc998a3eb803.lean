-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_hypotheses_seven_bc998a3eb803
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:24.926257+00:00
-- url     : https://prove2.me/submissions/16334e38-a0e5-4b71-ab0b-08371acde336

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_finrank_sevenQ_3d28983f8fd9
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_omega_sq_sevenQ_2845b5ee752b
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_card_embeddings_sevenQ_58dcab64038d

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution :
    Nat.Prime 7 ∧ 7 % 16 = 7 ∧ Module.finrank ℚ QuadraticFieldSqrtNegSeven = 2 ∧
      (∃ x : QuadraticFieldSqrtNegSeven, x ^ 2 = -((7 : ℕ) : QuadraticFieldSqrtNegSeven)) ∧ Nonempty (QuadraticFieldSqrtNegSeven →+* ℂ) :=
  ⟨by norm_num, rfl, finrank_sevenQ, ⟨_, omega_sq_sevenQ⟩,
    Fintype.card_pos_iff.mp (by rw [card_embeddings_sevenQ]; norm_num)⟩
end GroundTheory.Heights₂.Theta
