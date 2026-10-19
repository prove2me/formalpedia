-- Prove2me | solution 1 for RamanujanPetersson.tau_q_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:20:58.04323+00:00
-- url     : https://prove2.me/submissions/5d9978ed-76f2-424d-ae03-aced8bfb028c

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries

namespace RPTQ

noncomputable def G : ModularForm 𝒮ℒ 12 :=
  (1 / 1728 : ℂ) • (ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2))

lemma disc_eq : (ModularForm.discriminant : ℍ → ℂ) = G := by
  funext z
  rw [discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [G, smul_apply, sub_apply, coe_mcast, coe_pow, Pi.pow_apply,
    smul_eq_mul]
  ring

lemma qexp : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) =
    (1 / 1728 : ℂ) • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  rw [disc_eq, G, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma c4 (m : ℕ) : (qExpansion 1 E₄).coeff m = if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  split_ifs <;> push_cast <;> ring

lemma c6 (m : ℕ) : (qExpansion 1 E₆).coeff m = if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
  split_ifs <;> push_cast <;> ring

lemma s3 : ArithmeticFunction.sigma 3 1 = 1 ∧ ArithmeticFunction.sigma 3 2 = 9 ∧
    ArithmeticFunction.sigma 3 3 = 28 ∧ ArithmeticFunction.sigma 3 4 = 73 ∧
    ArithmeticFunction.sigma 3 5 = 126 := by
  simp only [ArithmeticFunction.sigma_apply]; decide

lemma s5 : ArithmeticFunction.sigma 5 1 = 1 ∧ ArithmeticFunction.sigma 5 2 = 33 ∧
    ArithmeticFunction.sigma 5 3 = 244 ∧ ArithmeticFunction.sigma 5 4 = 1057 ∧
    ArithmeticFunction.sigma 5 5 = 3126 := by
  simp only [ArithmeticFunction.sigma_apply]; decide

lemma tau_eq (n : ℕ) : (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n =
    (1 / 1728 : ℂ) * ((qExpansion 1 E₄ ^ 3).coeff n - (qExpansion 1 E₆ ^ 2).coeff n) := by
  rw [qexp, PowerSeries.coeff_smul, map_sub, smul_eq_mul]

theorem main : (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 0 = 0 ∧
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 1 = 1 ∧
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 2 = -24 ∧
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 3 = 252 ∧
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 4 = -1472 ∧
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 5 = 4830 := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := s3
  obtain ⟨b1, b2, b3, b4, b5⟩ := s5
  simp only [tau_eq, pow_succ, pow_zero, one_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_zero,
    c4, c6]
  norm_num [a1, a2, a3, a4, a5, b1, b2, b3, b4, b5]

end RPTQ

open RamanujanPetersson in
theorem solution :
    tau 0 = 0 ∧ tau 1 = 1 ∧ tau 2 = -24 ∧ tau 3 = 252 ∧ tau 4 = -1472 ∧ tau 5 = 4830 :=
  RPTQ.main
