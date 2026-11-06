-- Prove2me | solution 1 for RH.Transport.Reflected.compensated_reflected_exponent_with_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:42.068908+00:00
-- url     : https://prove2.me/submissions/159f4da3-6ea2-4d00-9f1b-9a4aeb351dfc

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_ReflectedExponent
import Theorems.Thm_RH_Transport_Reflected_hybrid_half_with_error
import Theorems.Thm_RH_Transport_Reflected_retained_kernel_quarter

set_option autoImplicit false
open RH RH.Transport RH.Transport.Reflected
noncomputable section
namespace RH.Transport.Reflected
theorem _root_.solution
    (E d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hO : -ε ≤ O₀) (hH : H ≤ (1 - E - 2 * d) - O₀ + ε)
    (hA : 2 * A₀ ≤ O₀ + ε) (hN : 0 ≤ N₀) (hNA : N₀ ≤ A₀)
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hell : ell₀ ≤ E - d + ε) (hz : za ≤ ell₀ + ε)
    (hv : -ε ≤ v) (hl : -ε ≤ ell) (he : -ε ≤ el) (hθ : |θ| ≤ ε)
    (hret : v + 3 * ell + el ≤
      2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀ + ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀) ≤
        1 - E - 2 * d + reflectedLoss E d + 40 * ε := by
  let Td := 2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀
  have hθlo : -ε ≤ θ := (abs_le.mp hθ).1
  have hθhi : θ ≤ ε := (abs_le.mp hθ).2
  have hTd : Td ≤ H - 3 * d + 6 * ε := by
    dsimp [Td]
    linarith
  have hcol : v + ell ≤ H + 10 * ε := by
    dsimp [Td] at hTd
    linarith
  have hmax : max H (v + ell) ≤ H + 10 * ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td - v - 3 * ell - el)
  have hloss0 : 0 ≤ reflectedLoss E d := by
    unfold reflectedLoss
    exact div_nonneg (le_max_left _ _) (by norm_num)
  have hloss : (5 * E - 1 + d) / 4 ≤ reflectedLoss E d := by
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num)
  by_cases hu : hybridSaving v za = za
  · unfold reflectedExponent
    rw [hu]
    change O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - za - ell -
      2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2 ≤ _
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v + 3 * ell + el)
    have hcharge : Td / 4 - 17 * ε / 12 ≤
        hybridSaving v za + ell + 2 * el / 3 +
          max 0 (Td - v - 3 * ell - el) / 2 := by
      have heq : Td - (v + 3 * ell + el) = Td - v - 3 * ell - el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        O₀ / 2 + H - S₀ - B₀ + za - Td / 4 + (10 + 17 / 12) * ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ _
    apply hbound.trans
    dsimp [Td]
    linarith
end RH.Transport.Reflected
