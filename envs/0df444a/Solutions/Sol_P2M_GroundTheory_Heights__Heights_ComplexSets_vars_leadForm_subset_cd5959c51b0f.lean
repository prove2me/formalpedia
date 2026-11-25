-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_vars_leadForm_subset_cd5959c51b0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:39.478974+00:00
-- url     : https://prove2.me/submissions/b7f51804-7be9-49d4-886d-9a439f7f7c41

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (f : MvPolynomial (Fin n) ℂ) : (leadForm f).vars ⊆ f.vars := by
  intro i hi
  rw [mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  refine ⟨d, ?_, hid⟩
  rw [mem_support_iff, leadForm, coeff_homogeneousComponent] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd
end GroundTheory.Heights₂.Heights.ComplexSets
