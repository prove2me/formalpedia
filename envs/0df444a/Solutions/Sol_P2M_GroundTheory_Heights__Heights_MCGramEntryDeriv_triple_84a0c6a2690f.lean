-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_triple_84a0c6a2690f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:18.204163+00:00
-- url     : https://prove2.me/submissions/b01a2fc7-286b-4806-b784-4d57e9509b62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv

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
open Matrix
open GroundTheory.Heights₂.Heights.MCGramEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GroundTheory.Heights₂.Heights.MCGramEntryDeriv
theorem _root_.solution {u v w : E → ℂ} {p : E} (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) (hw : DifferentiableAt ℝ w p) :
    DifferentiableAt ℝ (fun q => u q * v q * w q) p ∧
      ‖fderiv ℝ (fun q => u q * v q * w q) p‖ ≤
        ‖fderiv ℝ u p‖ * ‖v p‖ * ‖w p‖ + ‖u p‖ * ‖fderiv ℝ v p‖ * ‖w p‖ +
          ‖u p‖ * ‖v p‖ * ‖fderiv ℝ w p‖ := by
  have huv : DifferentiableAt ℝ (fun q => u q * v q) p := hu.mul hv
  refine ⟨huv.mul hw, ?_⟩
  rw [fderiv_fun_mul huv hw, fderiv_fun_mul hu hv]
  have h1 := norm_add_le ((u p * v p) • fderiv ℝ w p)
    (w p • (u p • fderiv ℝ v p + v p • fderiv ℝ u p))
  have h2 := norm_add_le (u p • fderiv ℝ v p) (v p • fderiv ℝ u p)
  rw [norm_smul, norm_smul, norm_mul] at h1
  rw [norm_smul, norm_smul] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (w p))
  nlinarith
end GroundTheory.Heights₂.Heights.MCGramEntryDeriv
