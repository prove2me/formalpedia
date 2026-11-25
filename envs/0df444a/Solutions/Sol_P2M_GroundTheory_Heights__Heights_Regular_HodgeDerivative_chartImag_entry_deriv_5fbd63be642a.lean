-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_chartImag_entry_deriv_5fbd63be642a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:05.078589+00:00
-- url     : https://prove2.me/submissions/fbf8c497-10df-4dcd-b293-02e9ba259524

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_cuspTime_hasFDerivAt_570f460d4fba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_im_hasFDerivAt_0386186e5479

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
theorem _root_.solution {n a g : ℕ} (h : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (p q : Fin g) {z : Fin n → ℂ}
    (hz : ∀ j, cuspCoord h z j ≠ 0) (hT : DifferentiableAt ℝ (fun y => T0 y p q) z) :
    DifferentiableAt ℝ (fun y => chartImag h T0 B y p q) z ∧
      ‖fderiv ℝ (fun y => chartImag h T0 B y p q) z‖ ≤
        ‖fderiv ℝ (fun y => T0 y p q) z‖ + ∑ i, |B i p q| * ‖cuspCoord h z i‖⁻¹ := by
  have e : (fun y => chartImag h T0 B y p q) =
      fun y => (T0 y p q).im + ∑ i, cuspTime h y i * B i p q := by
    funext y
    simp [chartImag, Matrix.sum_apply]
  choose L hL hLn using fun i => cuspTime_hasFDerivAt h i (hz i)
  obtain ⟨h0, h0n⟩ := im_hasFDerivAt hT
  have hsum : HasFDerivAt (fun y => ∑ i, cuspTime h y i * B i p q) (∑ i, B i p q • L i) z :=
    (HasFDerivAt.sum (u := Finset.univ) (A := fun i y => cuspTime h y i * B i p q)
      fun i _ => (hL i).mul_const (B i p q)).congr_of_eventuallyEq
        (Eventually.of_forall fun y => by simp only [Finset.sum_apply])
  have hall : HasFDerivAt (fun y => (T0 y p q).im + ∑ i, cuspTime h y i * B i p q)
      (Complex.imCLM.comp (fderiv ℝ (fun y => T0 y p q) z) + ∑ i, B i p q • L i) z := h0.add hsum
  rw [e]
  refine ⟨hall.differentiableAt, ?_⟩
  rw [hall.fderiv]
  refine (norm_add_le _ _).trans (add_le_add h0n ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hLn i) (abs_nonneg _)
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
