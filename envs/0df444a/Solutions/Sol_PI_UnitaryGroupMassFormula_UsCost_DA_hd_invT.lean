-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.hd_invT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:28.820963+00:00
-- url     : https://prove2.me/submissions/322d02d1-efaf-4869-b51c-5537db87b7ec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_c_det
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_conjT
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {t : ℝ}
namespace PI.UnitaryGroupMassFormula.UsCost.DA
theorem _root_.solution {a : ℕ} (B : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) (-Bᴴ) 0 := by
  have hL : HasDerivAt (fun t : ℝ => (1 + t • B)ᴴ) Bᴴ 0 := by
    have e : (fun t : ℝ => (1 + t • B)ᴴ) = fun t => 1 + t • Bᴴ := by
      funext t; simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    rw [e]
    exact (((hasDerivAt_id' (0 : ℝ)).smul_const Bᴴ).const_add (1 : Matrix (Fin a) (Fin a) ℂ)).congr_deriv (one_smul _ _)
  have hC : ContDiffAt ℝ 1 (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 :=
    cm_inv (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))) (by simp)
  have hCd := (hC.differentiableAt one_ne_zero).hasDerivAt
  have hP := hd_mul hCd hL
  have hcont : ContinuousAt (fun t : ℝ => ((1 + t • B)ᴴ).det) 0 :=
    (c_det (n := 0) (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)))).continuousAt
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 + t • B)ᴴ).det ≠ 0 := hcont.eventually_ne (by simp)
  have hev : (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hne] with t ht
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  have h0 : HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin a) (Fin a) ℂ)).congr_of_eventuallyEq hev
  have hu := h0.unique hP
  simp only [zero_smul, add_zero, Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Matrix.one_mul] at hu
  have : deriv (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 = -Bᴴ := eq_neg_of_add_eq_zero_left hu.symm
  exact hCd.congr_deriv this
end PI.UnitaryGroupMassFormula.UsCost.DA
