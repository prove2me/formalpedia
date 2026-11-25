-- Prove2me | solution 1 for PI.CompAtExist.val_eq_of_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:45.308729+00:00
-- url     : https://prove2.me/submissions/a8f1c77c-d1f6-479b-8e1d-1ad3e936296e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
namespace PI.CompAtExist
theorem _root_.solution {K : Type*} [Field K] (μ ν : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ x, μ x ≤ 1 ↔ ν x ≤ 1) {ϖ π : K} (hϖ : ν ϖ = WithZero.exp (-1))
    (hπ : μ π = WithZero.exp (-1)) (x : K) : μ x = ν x := by
  have hunit : ∀ (μ' ν' : Valuation K (WithZero (Multiplicative ℤ))), (∀ x, μ' x ≤ 1 ↔ ν' x ≤ 1) →
      ∀ y, ν' y = 1 → μ' y = 1 := by
    intro μ' ν' h' y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have h1 : μ' y ≤ 1 := (h' y).2 hy.le
    have h2 : μ' y⁻¹ ≤ 1 := (h' y⁻¹).2 (by rw [map_inv₀, hy, inv_one])
    have hm : μ' y⁻¹ * μ' y = 1 := by rw [← map_mul, inv_mul_cancel₀ hy0, map_one]
    have hle : μ' y⁻¹ * μ' y ≤ 1 * μ' y := mul_le_mul' h2 le_rfl
    rw [hm, one_mul] at hle
    exact le_antisymm h1 hle
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have key : ∀ y, y ≠ 0 → μ y * μ ϖ ^ (WithZero.log (ν y)) = 1 := by
    intro y hy
    have hνy : ν y ≠ 0 := ν.ne_zero_iff.2 hy
    have hνp : ν (ϖ ^ (WithZero.log (ν y))) ≠ 0 := ν.ne_zero_iff.2 (zpow_ne_zero _ hϖ0)
    have hne : ν (y * ϖ ^ (WithZero.log (ν y))) ≠ 0 := ν.ne_zero_iff.2 (mul_ne_zero hy (zpow_ne_zero _ hϖ0))
    have h1 : ν (y * ϖ ^ (WithZero.log (ν y))) = 1 := by
      rw [← WithZero.exp_log hne, map_mul, WithZero.log_mul hνy hνp,
        map_zpow₀, WithZero.log_zpow, hϖ, WithZero.log_exp, smul_eq_mul]
      rw [show WithZero.log (ν y) + WithZero.log (ν y) * (-1) = 0 by ring, WithZero.exp_zero]
    have h2 := hunit μ ν h _ h1
    rwa [map_mul, map_zpow₀] at h2
  have hμϖ0 : μ ϖ ≠ 0 := μ.ne_zero_iff.2 hϖ0
  have hμϖ : μ ϖ = WithZero.exp (-1) := by
    have k1 := congrArg WithZero.log (key π hπ0)
    rw [WithZero.log_mul (by rw [hπ]; exact WithZero.exp_ne_zero) (zpow_ne_zero _ hμϖ0), hπ,
      WithZero.log_exp, WithZero.log_zpow, WithZero.log_one, smul_eq_mul] at k1
    have hij : WithZero.log (ν π) * WithZero.log (μ ϖ) = 1 := by linarith
    have hlt : μ ϖ < 1 := by
      refine lt_of_le_of_ne ((h ϖ).2 (by rw [hϖ]; exact WithZero.exp_le_exp.2 (by norm_num))) ?_
      intro h1
      have := hunit ν μ (fun x => (h x).symm) ϖ h1
      rw [hϖ] at this
      have := congrArg WithZero.log this
      rw [WithZero.log_exp, WithZero.log_one] at this
      norm_num at this
    have hneg : WithZero.log (μ ϖ) < 0 := by
      have := (WithZero.log_le_log hμϖ0 one_ne_zero).2 hlt.le
      rw [WithZero.log_one] at this
      rcases lt_or_eq_of_le this with h' | h'
      · exact h'
      · exfalso
        have := WithZero.exp_log hμϖ0
        rw [h', WithZero.exp_zero] at this
        exact hlt.ne this.symm
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hij) with h' | h'
    · omega
    · rw [← WithZero.exp_log hμϖ0, h']
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have hμx : μ x ≠ 0 := μ.ne_zero_iff.2 hx
    have hνx : ν x ≠ 0 := ν.ne_zero_iff.2 hx
    have k2 := congrArg WithZero.log (key x hx)
    rw [WithZero.log_mul hμx (zpow_ne_zero _ hμϖ0), hμϖ, WithZero.log_zpow, WithZero.log_exp,
      WithZero.log_one, smul_eq_mul] at k2
    rw [← WithZero.exp_log hμx, ← WithZero.exp_log hνx]
    congr 1
    linarith
end PI.CompAtExist
