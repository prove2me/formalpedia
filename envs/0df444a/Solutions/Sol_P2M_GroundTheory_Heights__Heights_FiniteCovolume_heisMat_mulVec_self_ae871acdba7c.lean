-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_self_ae871acdba7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:28.698996+00:00
-- url     : https://prove2.me/submissions/709ee479-4846-4892-a561-cd0318a96ada

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
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
theorem _root_.solution {y : ι → ℂ} (hy : hForm H a y = 0) (s : ℂ) :
    heisMat H a y s *ᵥ a = a := by
  have hya : hForm H y a = 0 := by rw [← hForm_conj hH, hy, map_zero]
  rw [heisMat_mulVec, ha, hya]
  simp
end GroundTheory.Heights₂.Heights.FiniteCovolume
