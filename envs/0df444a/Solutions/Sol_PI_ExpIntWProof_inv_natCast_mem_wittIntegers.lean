-- Prove2me | solution 1 for PI.ExpIntWProof.inv_natCast_mem_wittIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:59.738218+00:00
-- url     : https://prove2.me/submissions/344bd2b9-f65a-4068-b6ec-470eb79589a8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Theorems.Thm_PI_ExpIntWProof_norm_p
import Theorems.Thm_PI_ExpIntWProof_norm_intCast_le_one
import Theorems.Thm_PI_ExpIntWProof_inv_mem_of_norm_sub_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (u : ℕ) (hu : ¬ p ∣ u) :
    ((u : ℂ_[p]))⁻¹ ∈ Wp p := by
  have hcop : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm
  have hb := Nat.gcd_eq_gcd_ab u p
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  set a : ℤ := Nat.gcdA u p
  set b : ℤ := Nat.gcdB u p
  set y : ℂ_[p] := (u : ℂ_[p]) * (a : ℂ_[p]) with hy
  have h1y : 1 - y = (p : ℂ_[p]) * (b : ℂ_[p]) := by
    have := congrArg (fun z : ℤ => (z : ℂ_[p])) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
    rw [hy, this]
    ring
  have hlt : ‖1 - y‖ < 1 := by
    rw [h1y, norm_mul, norm_p]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    calc (p : ℝ)⁻¹ * ‖(b : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (norm_intCast_le_one p b) (by positivity)
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hp1
  have hyW : y ∈ Wp p := mul_mem (natCast_mem _ u) (intCast_mem _ a)
  have hyinv := inv_mem_of_norm_sub_lt p hyW hlt
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, sub_zero, norm_one] at hlt
    exact lt_irrefl _ hlt
  have ha0 : (a : ℂ_[p]) ≠ 0 := fun h0 => hy0 (by rw [hy, h0, mul_zero])
  have hu0 : (u : ℂ_[p]) ≠ 0 := fun h0 => hy0 (by rw [hy, h0, zero_mul])
  have : ((u : ℂ_[p]))⁻¹ = (a : ℂ_[p]) * y⁻¹ := by
    rw [hy]
    field_simp
  rw [this]
  exact mul_mem (intCast_mem _ a) hyinv
end PI.ExpIntWProof
