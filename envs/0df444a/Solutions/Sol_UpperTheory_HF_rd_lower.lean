-- Prove2me | solution 1 for UpperTheory.HF.rd_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:06.701829+00:00
-- url     : https://prove2.me/submissions/f7695c6c-968b-4628-b7fb-9746dfc747e8

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RdLower
import Theorems.Thm_Formalism_HC_Frame_ord_le_o_mul_two_pow
import Theorems.Thm_Formalism_HC_Frame_two_pow_le_ord
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_sixteen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem rd_lower_num (e : ℕ) (he : 2 ≤ e) :
    (6.7 : ℝ) < (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) := by
  have he' : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have h1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ ((11 : ℝ) / 4) ≤ (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [he', h1])
  refine lt_of_lt_of_le ?_ h3
  have h4 : ((2 : ℝ) ^ ((11 : ℝ) / 4)) ^ (4 : ℕ) = 2 ^ (11 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_
  rw [h4]; norm_num
end

set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (6.7 : ℝ) < (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ∧ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) ≤ H.rd / Real.sqrt H.d ∧ 8 < H.rd / 2 ∧ 2 * 2 ^ φ.e ≤ 2 * φ.ord ∧ 2 * φ.ord ≤ 2 * φ.o * 2 ^ φ.e := by
  intro φ H
  have h1 := rd_lower_num φ.e H.two_le_e
  have h2 := H.der.rd_ge
  have hd : 7 ≤ H.d := by have := H.d_mod_sixteen; omega
  have hd' : (7 : ℝ) ≤ (H.d : ℝ) := by exact_mod_cast hd
  have hs : (2.6 : ℝ) ≤ Real.sqrt H.d := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < Real.sqrt H.d := by linarith
  refine ⟨h1, (le_div_iff₀ hs0).2 h2, ?_, Nat.mul_le_mul_left 2 φ.two_pow_le_ord, ?_⟩
  · have h3 : (6.7 : ℝ) * 2.6 ≤ (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d :=
      mul_le_mul h1.le hs (by norm_num) (by positivity)
    linarith
  · rw [mul_assoc]
    exact Nat.mul_le_mul_left 2 φ.ord_le_o_mul_two_pow
end UpperTheory.HF
