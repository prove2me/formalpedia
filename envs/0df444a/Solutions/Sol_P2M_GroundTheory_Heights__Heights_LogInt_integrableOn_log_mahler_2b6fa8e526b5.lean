-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:40.210068+00:00
-- url     : https://prove2.me/submissions/b852c5c5-c007-4cb2-a323-58b6a474ecbf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ballSet_subset_polydisc_628419bd91dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_normT_univ_01f1829fb5fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_logNormT_b092fe5ed6e3


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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  obtain ⟨h1, h2⟩ := logNormT h C hC0 hC Finset.univ f hf
  simp only [normT_univ] at h1 h2
  exact ⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC),
    ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩
end GroundTheory.Heights₂.Heights.LogInt
