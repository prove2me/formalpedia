-- Prove2me | solution 1 for PI.ExpIntWProof.Key.div_p_mem_of_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:14.000818+00:00
-- url     : https://prove2.me/submissions/7a0c3ae9-9717-4e38-a142-1994cb65b7b9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_rootsOfUnityRing_le_wittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_frob_congr
import Theorems.Thm_PI_ExpIntWProof_Key_inv_one_sub_mem
import Theorems.Thm_PI_ExpIntWProof_Key_natp_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.ExpIntWProof.Key
theorem _root_.solution {y : ℂ_[p]} (hy : y ∈ S0 p) (h : ‖y‖ < 1) : y / p ∈ Wp p := by
  obtain ⟨f, hf, z, hz, he⟩ := frob_congr y hy
  set q := p ^ f with hqdef
  have hpq : p ≤ q := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf
  have h2 : 2 ≤ q := le_trans hp.out.two_le hpq
  set ξ := y ^ (q - 1) with hξdef
  have hξW : ξ ∈ Wp p := rootsOfUnityRing_le_wittIntegers p (Subring.pow_mem _ hy _)
  have hξn : ‖ξ‖ < 1 := by
    rw [hξdef, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h (by omega)
  have hne : (1 - ξ) ≠ 0 := by
    intro h0
    have : ξ = 1 := (sub_eq_zero.1 h0).symm
    rw [this, norm_one] at hξn; exact lt_irrefl _ hξn
  have hyq : y * ξ = y ^ q := by
    rw [hξdef, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have h1 : y * (1 - ξ) = -((p : ℂ_[p]) * z) := by
    rw [mul_sub, mul_one, hyq, ← he]; ring
  have hval : y / p = -z * (1 - ξ)⁻¹ := by
    have hp0 := natp_ne_zero (p := p)
    rw [div_eq_iff hp0]
    calc y = y * (1 - ξ) * (1 - ξ)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ = -z * (1 - ξ)⁻¹ * p := by rw [h1]; ring
  rw [hval]
  exact Subring.mul_mem _ (Subring.neg_mem _ (rootsOfUnityRing_le_wittIntegers p hz)) (inv_one_sub_mem hξW hξn)
end PI.ExpIntWProof.Key
