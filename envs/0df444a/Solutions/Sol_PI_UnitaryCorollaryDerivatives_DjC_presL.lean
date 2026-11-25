-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.presL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:38.010642+00:00
-- url     : https://prove2.me/submissions/a4159f2c-9cd5-4071-b5c1-e2443b697d01

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_mem_range_eL
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_hpk_row

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable (k j ρ : ℕ)
variable {k j ρ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution {Y : B.Mat k (j + ρ)} (hY : inLieP k j ρ Y) : Pres (Set.range (eL k j ρ))ᶜ Y := by
  intro c b hb hc
  simp only [Set.mem_compl_iff, not_not, mem_range_eL] at hb hc
  have hcl := c.isLt
  have hi' : 2 * (j + ρ) + k - c.val < 2 * (j + ρ) + k + 1 := by omega
  obtain ⟨i, hidef⟩ : ∃ i : Fin (2 * (j + ρ) + k + 1), i = ⟨2 * (j + ρ) + k - c.val, hi'⟩ := ⟨_, rfl⟩
  have hiv : i.val = 2 * (j + ρ) + k - c.val := by rw [hidef]
  have hi : i.val < j := by omega
  have hL := congrArg (fun M : Matrix (Fin (2 * (j + ρ) + k + 1)) (Fin (2 * (j + ρ) + k + 1)) ℂ => M i b) hY.1
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply] at hL
  have h1 : ∑ m, Yᴴ i m * Hpk k (j + ρ) m b = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : m.val < j
    · rw [hpk_row m b (by omega), if_neg (by omega), mul_zero]
    · rw [Matrix.conjTranspose_apply, hY.2 m i hi (by omega), star_zero, zero_mul]
  have h2 : ∑ m, Hpk k (j + ρ) i m * Y m b = Y c b := by
    rw [Finset.sum_eq_single c]
    · rw [hpk_row i c (by omega), if_pos (by omega), one_mul]
    · intro m _ hm
      rw [hpk_row i m (by omega), if_neg, zero_mul]
      intro h
      apply hm
      ext
      omega
    · simp
  rw [h1, h2, zero_add] at hL
  exact hL
end PI.UnitaryCorollaryDerivatives.DjC
