-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_order_00de2034edca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:34.025572+00:00
-- url     : https://prove2.me/submissions/ca69f3b6-f225-497c-aea4-4f29f3c03b5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_periodic_fdce41a51a71
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_norm_exp_quad_le_0dcc304a5f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_castLE_f986c713271f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_mem_420aa9a2a999
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_update_mem_1d5836680385

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
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution (hD : LogCoverDescent.Statement) (hO : PuncturedExpOrder.Statement)
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (i : Fin a)
    (hne : ∀ j : Fin a, j ≠ i → z (Fin.castLE P.a_le j) ≠ 0) :
    0 ≤ intQuad (P.B i) v ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun x => Complex.exp (psi P v (Function.update z (Fin.castLE P.a_le i) x)))
        (𝓝[≠] 0) (𝓝 c) := by
  classical
  have hΨ := (hD n a P.a_le (phi P v) (phi_analytic P v) (phi_periodic P v)).1
  set C : ℂ := ∏ j ∈ Finset.univ.erase i, z (Fin.castLE P.a_le j) ^ intQuad (P.B j) v with hC
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
    zpow_ne_zero _ (hne j (Finset.ne_of_mem_erase hj))
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC0
  refine hO 1 (fun x => psi P v (Function.update z (Fin.castLE P.a_le i) x)) (intQuad (P.B i) v)
    ‖C‖⁻¹ one_pos ?_ ?_
  · intro x hx
    have hy := update_mem P hz i hne hx
    exact ((hΨ _ hy).differentiableAt.comp x
      (hasFDerivAt_update z x).differentiableAt).differentiableWithinAt
  · intro x hx
    have hy := update_mem P hz i hne hx
    have hw := logLift_mem P hy
    have hb := norm_exp_quad_le P v _ hw
    rw [exp_quad] at hb
    have hprod : Complex.exp (∑ j, logLift a (Function.update z (Fin.castLE P.a_le i) x)
        (Fin.castLE P.a_le j) * ((intQuad (P.B j) v : ℤ) : ℂ)) = x ^ intQuad (P.B i) v * C := by
      rw [Complex.exp_sum]
      have hj : ∀ j, Complex.exp (logLift a (Function.update z (Fin.castLE P.a_le i) x)
          (Fin.castLE P.a_le j) * ((intQuad (P.B j) v : ℤ) : ℂ)) =
          Function.update z (Fin.castLE P.a_le i) x (Fin.castLE P.a_le j) ^ intQuad (P.B j) v := by
        intro j
        rw [logLift_castLE P, mul_comm, Complex.exp_int_mul,
          Complex.exp_log (show Function.update z (Fin.castLE P.a_le i) x (Fin.castLE P.a_le j) ≠ 0
            from hy.2 j)]
      simp only [hj]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hC]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun j hj' => ?_
        rw [Function.update_of_ne (cusp_ne P (Finset.ne_of_mem_erase hj'))]
    rw [hprod, ← mul_assoc, norm_mul] at hb
    have hb' : ‖Complex.exp (psi P v (Function.update z (Fin.castLE P.a_le i) x)) *
        x ^ intQuad (P.B i) v‖ * ‖C‖ ≤ 1 := hb
    simpa [one_div] using (le_div_iff₀ hCpos).mpr hb'
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
