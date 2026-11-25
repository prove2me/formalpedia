-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_integral_LaG_97e56d9409a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:32.244697+00:00
-- url     : https://prove2.me/submissions/304973d0-6035-4191-b253-7d6846e2218e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_mem_LaG_ed2258b343aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_conj_mem_e10fd5f7b52f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
theorem _root_.solution : IsIntegralOn hG LaG := by
  intro x hx y hy
  rw [mem_LaG] at hx hy
  rw [hG_apply]
  exact sub_mem (mul_mem (conj_mem (hx 0)) (hy 0)) (mul_mem (conj_mem (hx 1)) (hy 1))
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
