-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_intersectionNumber_baseChange_380f38d27535
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:53.217788+00:00
-- url     : https://prove2.me/submissions/592ea3a4-f63c-4459-804f-e335c60382eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HasDerivAtDet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_hasDerivAt_det_93e893f6ccc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_sum_cramer_eq_ad784f2d7569

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Matrix Equiv
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace LogDetDerivative
theorem _root_.solution : LogDetDerivative.Statement := by
  intro m G G' hpos hG t
  have hdet := LogDetDerivative.hasDerivAt_det (hG t)
  rw [LogDetDerivative.sum_cramer_eq _ _ (hpos t).det_pos.ne'.isUnit] at hdet
  have hre : HasDerivAt (fun s ↦ (G s).det.re)
      ((G t).det * ((G t)⁻¹ * G' t).trace).re t := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdet
  have hp := (hpos t).det_pos
  rw [Complex.lt_def] at hp
  obtain ⟨hre0, him0⟩ := hp
  simp only [Complex.zero_re, Complex.zero_im] at hre0 him0
  have hlog := (hre.log hre0.ne').const_mul (-(1 / 2) : ℝ)
  refine hlog.congr_deriv ?_
  rw [Complex.mul_re, ← him0, zero_mul, sub_zero]
  field_simp
end LogDetDerivative
end GroundTheory.Heights₂.Heights.HilbertSamuel
