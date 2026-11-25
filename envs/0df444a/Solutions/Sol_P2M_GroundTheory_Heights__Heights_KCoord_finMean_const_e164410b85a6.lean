-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KCoord_finMean_const_e164410b85a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:04.783275+00:00
-- url     : https://prove2.me/submissions/38112032-501c-4bb0-9dcb-0024b7221fcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordWeak
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_card_pos_real_b5d9ffd13cbb

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
open Real
open GroundTheory.Heights₂.Heights.KCoord
variable {S : Type*} [Fintype S]
namespace GroundTheory.Heights₂.Heights.KCoord
theorem _root_.solution [Nonempty S] (c : ℝ) : finMean (fun _ : S => c) = c := by
  have h := (card_pos_real (S := S)).ne'
  simp only [finMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
end GroundTheory.Heights₂.Heights.KCoord
