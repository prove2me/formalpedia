-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HadamardPSD_proof_387a52e4845c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:24.54218+00:00
-- url     : https://prove2.me/submissions/fed04ba5-cbf8-45de-87f8-6ed92735291a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHadamardPSD
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardPSDAux_det_eq_zero_of_diag_eq_zero_459d5de6f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardPSDAux_le_of_diag_pos_7e09ecc94e55

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
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights
namespace HadamardPSD
theorem _root_.solution : HadamardPSD.Statement := by
  intro n A hA
  by_cases h : ∃ i, A i i = 0
  · obtain ⟨i, hi⟩ := h
    rw [HadamardPSDAux.det_eq_zero_of_diag_eq_zero hA hi, norm_zero]
    exact prod_nonneg fun _ _ => norm_nonneg _
  · push Not at h
    refine HadamardPSDAux.le_of_diag_pos hA fun i => ?_
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    rcases hre.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm him.symm) (h i)
end HadamardPSD
end GroundTheory.Heights₂.Heights
