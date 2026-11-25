-- Prove2me | solution 1 for PI.WGL.LTE.colWt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:41.081493+00:00
-- url     : https://prove2.me/submissions/02619be1-e880-4af2-b78a-8f1a278ea8b5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Theorems.Thm_PI_WGL_LTE_lam_natW_val
import Theorems.Thm_PI_WGL_LTE_aLast_val
import Theorems.Thm_PI_WGL_LTE_b_val
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_LTD_card_lt_sz
import Theorems.Thm_PI_WGL_LTD_natW_sg_val
import Theorems.Thm_PI_WGL_LTD_sum_ite_val
import Theorems.Thm_PI_WGL_LTD_sz_lt
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
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : colWt h lam sg sz L = lam.natW := by
  classical
  funext t
  obtain ⟨tv, htv⟩ := t
  unfold colWt
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]

  have hP : (∑ i : Fin n, (if i.1 + 1 = n then (aa h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * initW N (n - 1 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (aa h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) (n - 1)]
    apply Finset.sum_congr rfl
    intro i _
    have := i.2
    by_cases hi : i.1 + 1 = n
    · rw [if_pos hi, if_pos (by omega)]
    · rw [if_neg hi, if_neg (by omega), zero_mul]
  have hQ : (∑ i : Fin n, (if i.1 = 0 then (bb h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * initW N (0 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) 0]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 = 0
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, zero_mul]

  have hK : (∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k)) ⟨tv, htv⟩) =
      (Finset.univ.filter fun k => tv < sz k).card +
        (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ L
    · simp only [hk, if_true, true_and, initW]
      split_ifs <;> omega
    · simp only [hk, if_false, false_and, initW]
      split_ifs <;> omega
  rw [hP, hQ, hK]
  by_cases htn : tv < n
  · have hn : 0 < n := by omega
    have h1 := card_lt_sz sg sz hshape ⟨tv, htn⟩
    have h2 := hL.2 ⟨tv, htn⟩
    simp only at h1 h2
    rw [h1, h2, dif_pos (by omega), dif_pos hn]
    have e1 := natW_sg_val sg ⟨tv, htn⟩
    have e2 := lam_natW_val h lam tv htv
    have e3 := aLast_val h lam sg hI hn
    have e4 := b_val h lam sg hI tv htn
    have hw1 : initW N (n - 1 + 1) ⟨tv, htv⟩ = 1 := by simp only [initW]; rw [if_pos (by simp; omega)]
    rw [hw1, mul_one]
    by_cases ht0 : tv = 0
    · subst ht0
      have hw2 : initW N (0 + 1) ⟨0, htv⟩ = 1 := by simp [initW]
      rw [hw2, mul_one, if_pos rfl]
      simp only at e1 e2 e3 e4 ⊢
      have := sg.anti (show (⟨0, htn⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by rw [Fin.le_def]; simp)
      omega
    · have hw2 : initW N (0 + 1) ⟨tv, htv⟩ = 0 := by simp only [initW]; rw [if_neg (by simp; omega)]
      rw [hw2, mul_zero, if_neg ht0]
      simp only at e1 e2 e3 e4 ⊢
      omega
  · have htn' : tv = n := by omega
    subst htn'
    have h1 : (Finset.univ.filter fun k => tv < sz k).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro k _; have := hsz k; omega
    have h2 : (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      have := hL.1 k hk.1
      rcases sz_lt sg sz hsz hshape k with h3 | h3 <;> omega
    rw [h1, h2]
    have e2 := lam_natW_val h lam tv htv
    have hz : lam.natW ⟨tv, htv⟩ = 0 := by
      have : (⟨tv, htv⟩ : Fin N) = ⟨tv, by omega⟩ := rfl
      omega
    rw [hz]
    have hw1 : ∀ j, j ≤ tv → initW N j ⟨tv, htv⟩ = 0 := by
      intro j hj; simp only [initW]; rw [if_neg (by simp; omega)]
    split_ifs with ha hb
    · rw [hw1 _ (by omega), hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · simp
end PI.WGL.LTE
