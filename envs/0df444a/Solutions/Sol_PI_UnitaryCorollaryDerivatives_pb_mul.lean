-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:39.91919+00:00
-- url     : https://prove2.me/submissions/c6db62d0-5d4b-4351-99f6-2a115df19f37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_ck
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_nonneg
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_Dw_mulL
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_leib_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {e₁ e₂ : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e₁ f) (hh : PG e₂ h) :
    PG (e₁ + e₂) (fun g => f g * h g) := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) :=
    ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).contDiff.comp hf.1
  refine ⟨hf.1.mul hh.1, fun n => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := pb_nonneg hf n
  obtain ⟨C₂, hC₂0, hC₂⟩ := pb_nonneg hh n
  refine ⟨2 ^ n * (C₁ * C₂), fun w hw hl g hg => ?_⟩
  have hw' : ∀ x ∈ w, B.inLie k r x.2 := fun x hx => (hw x hx).1
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) w.length
      (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h :=
    ⟨pb_ck hcd _, pb_ck hh.1 _, fun _ _ hg => hg.elim⟩
  have hp := gN_pos hg
  have hp1 : 0 ≤ B.gN g ^ e₁ := Real.rpow_nonneg hp.le _
  have hp2 : 0 ≤ B.gN g ^ e₂ := Real.rpow_nonneg hp.le _
  have hM : 0 ≤ C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂) :=
    mul_nonneg (mul_nonneg hC₁0 hp1) (mul_nonneg hC₂0 hp2)
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂)) w
    (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h hw' hP (by
      intro w₁ w₂ h₁ h₂ _
      have u1 : ∀ x ∈ w₁, B.unitLie k r x.2 := fun x hx => hw x (h₁.subset hx)
      have u2 : ∀ x ∈ w₂, B.unitLie k r x.2 := fun x hx => hw x (h₂.subset hx)
      rw [pb_Dw_mulL (fun x hx => (u1 x hx).1) (pb_ck hf.1 _) g hg]
      exact mul_le_mul ((ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans
          (hC₁ w₁ u1 (h₁.length_le.trans hl) g hg))
        (hC₂ w₂ u2 (h₂.length_le.trans hl) g hg) (norm_nonneg _) (mul_nonneg hC₁0 hp1))
  have e1 : (fun g => f g * h g) = ap (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h := by
    funext g; simp [ap]
  rw [e1]
  refine hb.trans ?_
  rw [Real.rpow_add hp]
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hl
  calc (2 : ℝ) ^ w.length * (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂))
      ≤ 2 ^ n * (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (C₁ * C₂) * (B.gN g ^ e₁ * B.gN g ^ e₂) := by ring
end PI.UnitaryCorollaryDerivatives
