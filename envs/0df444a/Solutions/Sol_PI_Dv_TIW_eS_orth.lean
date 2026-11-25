-- Prove2me | solution 1 for PI.Dv.TIW.eS_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:39.076529+00:00
-- url     : https://prove2.me/submissions/4fb1fd43-8f09-4242-9543-fa607ff71a47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Theorems.Thm_PI_Dv_TIW_coeff_sum_of
import Theorems.Thm_PI_Dv_TIW_eS_ne_zero
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_eS_central
import Theorems.Thm_PI_Dv_TIW_eS_idem
import Theorems.Thm_PI_Dv_TIW_mul_eS
import Theorems.Thm_PI_Dv_TIW_tau_central_scalar
import Theorems.Thm_PI_Dv_TIW_theta_one
import Theorems.Thm_PI_Dv_TIW_theta_smul
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
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G)
namespace PI.Dv.TIW
theorem _root_.solution (s t : T.S) (hst : s ≠ t) : eS T s * eS T t = 0 := by
  obtain ⟨μ, hμ⟩ := tau_central_scalar T t (eS T s) (fun z => eS_central T s z)
  obtain ⟨ν, hν⟩ := tau_central_scalar T s (eS T t) (fun z => eS_central T t z)
  have h1 : eS T s * eS T t = μ • eS T t := by rw [mul_eS T t, hμ, theta_smul, theta_one]
  have h2 : eS T s * eS T t = ν • eS T s := by
    rw [← eS_central T t (eS T s), mul_eS T s, hν, theta_smul, theta_one]
  by_contra hne
  have hμ0 : μ ≠ 0 := fun h => hne (by rw [h1, h, zero_smul])
  have h3 : eS T t = (μ⁻¹ * ν) • eS T s := by
    rw [mul_smul, ← h2, h1, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  set κ := μ⁻¹ * ν with hκ
  have hsne := eS_ne_zero T s
  have htne := eS_ne_zero T t
  have h4 : κ = 1 := by
    have e1 : eS T t = (κ * κ) • eS T s := by
      conv_lhs => rw [← eS_idem T t, h3]
      rw [smul_mul_smul_comm, eS_idem]
    have e2 : (κ * κ - κ) • eS T s = 0 := by rw [sub_smul, ← e1, ← h3, sub_self]
    rcases smul_eq_zero.mp e2 with h | h
    · have hκ0 : κ ≠ 0 := fun h0 => htne (by rw [h3, h0, zero_smul])
      have : κ * (κ - 1) = 0 := by rw [mul_sub, mul_one]; exact h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hκ0
      · exact sub_eq_zero.mp h'
    · exact absurd h hsne
  have h5 : eS T t = eS T s := by rw [h3, h4, one_smul]
  have hc : ∀ g : G, (((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W t) (T.tau t g⁻¹)) = (((Module.finrank K (T.W s) : ℕ) : K) /
      ((Fintype.card G : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s g⁻¹)) := by
    intro g
    have := congrArg (fun z : MonoidAlgebra K G => z.coeff g) h5
    simp only [eS] at this
    rwa [coeff_sum_of, coeff_sum_of] at this
  have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : Module.finrank K (T.W t) = Module.finrank K (T.W s) := by
    have := hc 1
    simp only [inv_one, map_one, LinearMap.trace_one] at this
    field_simp at this
    have h' : ((Module.finrank K (T.W t) ^ 2 : ℕ) : K) = ((Module.finrank K (T.W s) ^ 2 : ℕ) : K) := by
      push_cast; linear_combination this
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) (by exact_mod_cast h')
  have hdK : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0 := by
    have : 0 < Module.finrank K (T.W s) := Module.finrank_pos
    exact_mod_cast this.ne'
  apply hst
  apply T.inj
  funext g
  have := hc g⁻¹
  rw [hd, inv_inv] at this
  have hne0 : ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0 := div_ne_zero hdK hG0
  exact (mul_left_cancel₀ hne0 this).symm
end PI.Dv.TIW
