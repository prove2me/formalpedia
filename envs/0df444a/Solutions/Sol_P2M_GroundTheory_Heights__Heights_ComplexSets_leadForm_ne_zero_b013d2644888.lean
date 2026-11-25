-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_leadForm_ne_zero_b013d2644888
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:12.600582+00:00
-- url     : https://prove2.me/submissions/22e3e697-d7fd-488c-82ae-b71789dfbf1f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


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
theorem _root_.solution {f : MvPolynomial (Fin n) ℂ} (hf : f ≠ 0) : leadForm f ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => m.sum fun _ e => e)
  intro h0
  have hc := congrArg (coeff d) h0
  rw [leadForm, coeff_homogeneousComponent, coeff_zero] at hc
  rw [if_pos (by rw [totalDegree, hdeg]; rfl)] at hc
  exact (mem_support_iff.mp hd) hc
end GroundTheory.Heights₂.Heights.ComplexSets
