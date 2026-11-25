-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mul_0b194300fa17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:31.177879+00:00
-- url     : https://prove2.me/submissions/c4168511-5368-45b7-949f-4f70c0b05f63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_left_21ed53f20908
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
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
theorem _root_.solution {y₁ y₂ : ι → ℂ} (h₁ : hForm H a y₁ = 0) (h₂ : hForm H a y₂ = 0)
    (s₁ s₂ : ℂ) :
    heisMat H a y₁ s₁ * heisMat H a y₂ s₂ =
      heisMat H a (y₁ + y₂) (s₁ + s₂ - hForm H y₁ y₂) := by
  have hya : hForm H y₁ a = 0 := by rw [← hForm_conj hH, h₁, map_zero]
  refine matrix_ext_mulVec fun z => ?_
  rw [← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec, heisMat_mulVec]
  simp only [hForm_add_right, hForm_sub_right, hForm_smul_right, hForm_add_left, ha, h₂, hya]
  module
end GroundTheory.Heights₂.Heights.FiniteCovolume
