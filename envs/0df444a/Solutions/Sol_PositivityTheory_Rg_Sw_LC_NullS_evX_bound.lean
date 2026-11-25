-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.evX_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:05.462561+00:00
-- url     : https://prove2.me/submissions/cf33a505-fe38-4110-b259-23a21912c96c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareNormBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_evX_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_norm_crd_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (P : PX m n) : ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ x, ‖evX P x‖ ≤ K * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨K1, d1, h1, b1⟩ := hp
    obtain ⟨K2, d2, h2, b2⟩ := hq
    refine ⟨K1 + K2, max d1 d2, by positivity, fun x => ?_⟩
    have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ max d1 d2 := pow_le_pow_right₀ hx (le_max_left _ _)
    have e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ max d1 d2 := pow_le_pow_right₀ hx (le_max_right _ _)
    calc ‖evX (p + q) x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := by simpa [evX_eq] using norm_add_le _ _
      _ ≤ K1 * (1 + ‖x‖) ^ d1 + K2 * (1 + ‖x‖) ^ d2 := add_le_add (b1 x) (b2 x)
      _ ≤ K1 * (1 + ‖x‖) ^ max d1 d2 + K2 * (1 + ‖x‖) ^ max d1 d2 :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (K1 + K2) * (1 + ‖x‖) ^ max d1 d2 := by ring
  | mul_X p k hp =>
    obtain ⟨K, d, hK, b⟩ := hp
    refine ⟨K, d + 1, hK, fun x => ?_⟩
    have hc : ‖crd k x‖ ≤ 1 + ‖x‖ := (norm_crd_le k x).trans (by linarith)
    calc ‖evX (p * X k) x‖ = ‖evX p x‖ * ‖crd k x‖ := by simp [evX_eq]
      _ ≤ (K * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul (b x) hc (norm_nonneg _) (by positivity)
      _ = K * (1 + ‖x‖) ^ (d + 1) := by ring
end PositivityTheory.Rg.Sw.LC.NullS
