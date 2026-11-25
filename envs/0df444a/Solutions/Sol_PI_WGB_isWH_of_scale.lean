-- Prove2me | solution 1 for PI.WGB.isWH_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:43.069691+00:00
-- url     : https://prove2.me/submissions/6dc00902-a11a-48c4-bf95-6817a01d1d1b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_coeff_scale
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (κ : Fin n → ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ t : Fin n → ℂˣ, aeval (fun v : Fin n × Fin n => C ((t v.2 : ℂ)) * X v) P =
      C (∏ i, (t i : ℂ) ^ κ i) * P) :
    IsWeightedHomogeneous (colW n n) P κ := by
  classical
  intro m hm
  funext s
  let t : Fin n → ℂˣ := fun i => if i = s then Units.mk0 2 two_ne_zero else 1
  have h0 := coeff_scale (fun i => (t i : ℂ)) P m
  rw [h t, coeff_C_mul] at h0
  have h2 := (mul_right_cancel₀ hm h0).symm
  have ht : ∀ i, (t i : ℂ) = if i = s then 2 else 1 := by
    intro i; simp only [t]; split_ifs <;> simp
  simp only [ht, Finsupp.prod, ite_pow, one_pow] at h2
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum,
    Finset.prod_ite_eq' Finset.univ s, if_pos (Finset.mem_univ _)] at h2
  have h3 : ∑ v ∈ m.support with v.2 = s, m v = κ s := by
    have h4 : ((2 ^ (∑ v ∈ m.support with v.2 = s, m v) : ℕ) : ℂ) = ((2 ^ κ s : ℕ) : ℂ) := by
      push_cast; exact h2
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h4)
  rw [← h3, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [colW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hv : v.2 = s
  · simp [hv]
  · simp [hv, Ne.symm hv]
end PI.WGB
