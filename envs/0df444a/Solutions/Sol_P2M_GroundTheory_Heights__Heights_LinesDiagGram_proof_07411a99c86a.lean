-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesDiagGram_proof_07411a99c86a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:45.636732+00:00
-- url     : https://prove2.me/submissions/8908e827-b77b-41b7-a822-77e569f63801

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesDiagGram
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesDiagGram_embVec_single_8a02013ef856

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
open KLinesDiagGram
namespace GroundTheory.Heights₂.Heights
namespace LinesDiagGram
theorem _root_.solution : LinesDiagGram.Statement := by
  intro K _ n d σ k τ hτ
  ext j j'
  simp only [gramAt, embVec_single, Matrix.diagonal_apply]
  rw [show (star (Pi.single (τ j) (1 : ℂ)) : Fin n → ℂ) = Pi.single (τ j) 1 by
    funext y; simp only [Pi.star_apply, Pi.single_apply]; split_ifs <;> simp]
  rw [single_dotProduct, one_mul, Matrix.mulVec_diagonal]
  simp only [Pi.single_apply, hτ.eq_iff]
  split_ifs with h
  · subst h; simp
  · simp
end LinesDiagGram
end GroundTheory.Heights₂.Heights
