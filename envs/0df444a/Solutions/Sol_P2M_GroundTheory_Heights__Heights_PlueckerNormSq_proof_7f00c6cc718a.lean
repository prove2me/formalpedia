-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlueckerNormSq_proof_7f00c6cc718a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:49.395018+00:00
-- url     : https://prove2.me/submissions/6bd749d8-61e9-4b5e-a2f0-389120aeefee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerNormSq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_onePipe_mul_conjTranspose_f82578e1cf02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerNormSqAlt_rowsOf_conjTranspose_e6b7b0baa3b1

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
open Matrix Finset
noncomputable section
open PlueckerNormSqAlt
namespace GroundTheory.Heights₂.Heights
namespace PlueckerNormSq
theorem _root_.solution (h : CauchyBinet.Statement) : PlueckerNormSq.Statement := by
  intro j m Z
  rw [← onePipe_mul_conjTranspose, h ℂ j (j + m) (onePipe Z) (onePipe Z)ᴴ]
  push_cast
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [rowsOf_conjTranspose, det_conjTranspose, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl
end PlueckerNormSq
end GroundTheory.Heights₂.Heights
