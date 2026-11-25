-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.norm_dS_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:18.526311+00:00
-- url     : https://prove2.me/submissions/12e5cd14-6434-4db5-b835-e9423144eebc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_fexp_gap
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_fix
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_inv_eq
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_n_ut


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) (i j) :
    ‖(dS k r s * n * (dS k r s)⁻¹ - 1) i j‖ ≤ s * ‖n i j‖ := by
  have hs := hs0.ne'
  rw [dS_inv_eq hs, Matrix.sub_apply]
  by_cases hfix : n i j = if i = j then 1 else 0
  · rw [dS_conj_fix hs i j hfix, Matrix.one_apply, sub_self, norm_zero]
    positivity
  · have hlt : i.val < j.val := by
      by_contra hle
      exact hfix (n_ut hn i j (by omega))
    have hne : i ≠ j := fun e => by rw [e] at hlt; omega
    have hW : ¬ (inW k r i ∧ inW k r j) := by
      rintro ⟨⟨hi1, -⟩, -, hj2⟩
      exact hfix (((mem_Nset_iff n).mp hn).2 i j hj2 (by omega))
    have hd := fexp_gap hlt hW
    rw [dS_conj_apply, Matrix.one_apply_ne hne, sub_zero, norm_mul, norm_mul, norm_zpow, norm_zpow,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs0.le,
      Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
    have key : s ^ fexp k r i * s⁻¹ ^ fexp k r j = s ^ (fexp k r i - fexp k r j) := by
      rw [_root_.inv_zpow, ← _root_.zpow_neg, ← zpow_add₀ hs, sub_eq_add_neg]
    have hle : s ^ (fexp k r i - fexp k r j) ≤ s := by
      calc s ^ (fexp k r i - fexp k r j) ≤ s ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hs0 hs1 hd
        _ = s := zpow_one s
    calc s ^ fexp k r i * ‖n i j‖ * s⁻¹ ^ fexp k r j = s ^ (fexp k r i - fexp k r j) * ‖n i j‖ := by
          rw [← key]; ring
      _ ≤ s * ‖n i j‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
end PI.QuotSetU.UnitaryGroupMassFormula.SW
