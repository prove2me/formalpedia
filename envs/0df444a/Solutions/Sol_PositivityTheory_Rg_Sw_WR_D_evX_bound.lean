-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.evX_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:09.199529+00:00
-- url     : https://prove2.me/submissions/1a0174cd-265d-49b0-aaae-eaf3a9c74d0a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisMore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_coord_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (P : PX m n) : ∃ (C : ℝ) (d : ℕ), ∀ x : Fin m → Fin n → ℂ, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, fun x => by simp [evX]⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1⟩ := hp
    obtain ⟨C2, d2, h2⟩ := hq
    refine ⟨|C1| + |C2|, d1 + d2, fun x => ?_⟩
    have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ (d1 + d2) := pow_le_pow_right₀ h0 (by omega)
    have e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ (d1 + d2) := pow_le_pow_right₀ h0 (by omega)
    have f1 : C1 * (1 + ‖x‖) ^ d1 ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
    have f2 : C2 * (1 + ‖x‖) ^ d2 ≤ |C2| * (1 + ‖x‖) ^ (d1 + d2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    calc ‖evX (p + q) x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := by
          simp only [evX, map_add]; exact norm_add_le _ _
      _ ≤ C1 * (1 + ‖x‖) ^ d1 + C2 * (1 + ‖x‖) ^ d2 := add_le_add (h1 x) (h2 x)
      _ ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) + |C2| * (1 + ‖x‖) ^ (d1 + d2) := add_le_add f1 f2
      _ = (|C1| + |C2|) * (1 + ‖x‖) ^ (d1 + d2) := by ring
  | mul_X p v hp =>
    obtain ⟨C, d, h⟩ := hp
    refine ⟨|C|, d + 1, fun x => ?_⟩
    have hv : ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ ≤ 1 + ‖x‖ := by
      have := norm_coord_le x v.1 v.2.1
      by_cases hb : v.2.2 <;> simp [hb] <;> linarith
    have hC : ‖evX p x‖ ≤ |C| * (1 + ‖x‖) ^ d :=
      (h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    calc ‖evX (p * MvPolynomial.X v) x‖
        = ‖evX p x‖ * ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ := by
          by_cases hb : v.2.2 <;> simp [evX, hb]
      _ ≤ (|C| * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul hC hv (norm_nonneg _) (by positivity)
      _ = |C| * (1 + ‖x‖) ^ (d + 1) := by ring
end PositivityTheory.Rg.Sw.WR.D
