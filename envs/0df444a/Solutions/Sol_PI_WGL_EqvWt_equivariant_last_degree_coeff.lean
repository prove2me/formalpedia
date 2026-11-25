-- Prove2me | solution 1 for PI.WGL.EqvWt.equivariant_last_degree_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:21.469806+00:00
-- url     : https://prove2.me/submissions/54d0eda2-2066-4900-8f6f-5a2464223b6e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_PI_WGL_EqvWt_coeff_sqAct_diag
import Theorems.Thm_PI_WGL_EqvWt_sum_rowDeg_of_mem
import Theorems.Thm_PI_WGL_EqvWt_sum_natW
import Theorems.Thm_PI_WGL_EqvWt_two_zpow_inj
import Theorems.Thm_PI_WGL_EqvWt_coeff_eq_of_eqv
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : coeff m (φ s) ≠ 0) :
    ((rowDeg m (Fin.last n) : ℕ) : ℤ) = wsum lam - wsum mu - lam.detShift := by
  set t : Fin n → ℂˣ := fun _ => Units.mk0 (2 : ℂ) two_ne_zero with ht
  have htv : ∀ i, (t i : ℂ) = 2 := fun _ => rfl
  have hκ : sqAct ℂ n mu (diagGL ℂ n t) s =
      ((∏ i : Fin n, (t i : ℂ)) ^ mu.detShift * (2 : ℂ) ^ (∑ j, mu.natW j)) • s := by
    ext m'
    rw [coeff_sqAct_diag, coeff_smul, smul_eq_mul]
    by_cases h0 : coeff m' s = 0
    · simp [h0]
    · have hs' := sum_rowDeg_of_mem mu s hs m' h0
      simp only [htv, Finset.prod_pow_eq_pow_sum, hs']
      ring
  have h1 := coeff_eq_of_eqv lam mu φ hφ t s hs _ hκ m hm
  simp only [htv, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum] at h1
  have hz : ∀ (a : ℕ) (d : ℤ), ((2 : ℂ) ^ a) ^ d = (2 : ℂ) ^ ((a : ℤ) * d) := by
    intro a d
    rw [← zpow_natCast, ← zpow_mul]
  have hn : ∀ a : ℕ, (2 : ℂ) ^ a = (2 : ℂ) ^ (a : ℤ) := fun a => (zpow_natCast 2 a).symm
  rw [hz, hz, hn (∑ i : Fin n, rowDeg m (Fin.castSucc i)), hn (∑ j, mu.natW j),
    ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0), ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] at h1
  have E := two_zpow_inj h1
  have hmem : φ s ∈ nablaSq ℂ (n + 1) lam := hφ.1 s hs
  have T := sum_rowDeg_of_mem lam (φ s) hmem m hm
  rw [Fin.sum_univ_castSucc] at T
  have SL := sum_natW lam
  have SM := sum_natW mu
  have T' : ((∑ i : Fin n, rowDeg m (Fin.castSucc i) : ℕ) : ℤ) + (rowDeg m (Fin.last n) : ℤ) =
      ((∑ j, lam.natW j : ℕ) : ℤ) := by exact_mod_cast T
  push_cast at E SL SM T' ⊢
  linear_combination (-1 : ℤ) * E + T' + SL - SM
end PI.WGL.EqvWt
