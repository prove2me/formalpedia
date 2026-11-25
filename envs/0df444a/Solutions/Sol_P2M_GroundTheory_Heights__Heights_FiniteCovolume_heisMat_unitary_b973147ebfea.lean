-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:12:53.349279+00:00
-- url     : https://prove2.me/submissions/7fa9e806-c408-4fa9-8e2a-5f82c5362d3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_left_21ed53f20908
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_left_b196893870d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_left_c1f6b63ea674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_of_hForm_1ab14222c8c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {y : ι → ℂ} (hy : hForm H a y = 0) {s : ℂ}
    (hs : s + starRingEnd ℂ s + hForm H y y = 0) :
    (heisMat H a y s)ᴴ * H * heisMat H a y s = H := by
  have hya : hForm H y a = 0 := by rw [← hForm_conj hH, hy, map_zero]
  refine unitary_of_hForm H fun p q => ?_
  rw [heisMat_mulVec, heisMat_mulVec]
  simp only [hForm_add_right, hForm_sub_right, hForm_smul_right, hForm_add_left, hForm_sub_left,
    hForm_smul_left, ha, hy, hya, hForm_conj hH]
  linear_combination (hForm H a q * hForm H p a) * hs
end GroundTheory.Heights₂.Heights.FiniteCovolume
