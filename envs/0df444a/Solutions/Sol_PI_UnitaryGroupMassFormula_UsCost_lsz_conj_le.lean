-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.lsz_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:35.189784+00:00
-- url     : https://prove2.me/submissions/1b5fb4dc-ccf2-4168-95f5-492e48f30e28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_EB_inv_hpk
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_one_le_gN_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_mx_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k r : ℕ} (n M : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) {c : ℝ} (hM : EB M c)
    (hc : 0 ≤ c) :
    lsz (n⁻¹ * M * n) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 4 * (1 + c) * B.gN n ^ 2 := by
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (by omega)
  have hg : 0 ≤ B.gN n := Real.sqrt_nonneg _
  have h := EB_mulF (EB_mulF (EB_inv_hpk n hu) hM) (fun i j => entry_le_gN n i j)
  have hmx : mx (n⁻¹ * M * n) ≤ N ^ 4 * c * B.gN n ^ 2 := by
    refine mx_le (h.mono (le_of_eq (by simp only [N]; ring))) (by positivity)
  have h1 : 1 ≤ N ^ 3 * B.gN n ^ 2 := one_le_gN_sq n hu
  have h3 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have h4 : 0 ≤ B.gN n ^ 2 := sq_nonneg _
  have h5 : N ^ 3 * B.gN n ^ 2 ≤ N ^ 4 * B.gN n ^ 2 := mul_le_mul_of_nonneg_right h3 h4
  have h6 : 0 ≤ N ^ 4 * B.gN n ^ 2 * c := by positivity
  unfold lsz
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith
end PI.UnitaryGroupMassFormula.UsCost
