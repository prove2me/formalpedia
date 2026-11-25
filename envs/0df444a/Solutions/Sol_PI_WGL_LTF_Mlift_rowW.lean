-- Prove2me | solution 1 for PI.WGL.LTF.Mlift_rowW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:10.197373+00:00
-- url     : https://prove2.me/submissions/42092345-66b8-4068-8179-b2d3fbe33cde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTuple
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_LTD_sum_ite_val
import Theorems.Thm_PI_WGL_LTE_aLast_val
import Theorems.Thm_PI_WGL_LTE_lam_detShift
import Theorems.Thm_PI_WGL_LTE_sg_detShift
import Theorems.Thm_PI_WGL_LTF_G_rowW
import Theorems.Thm_PI_WGL_LTF_cardL
import Theorems.Thm_PI_WGL_LTF_constant_weight_apply
import Theorems.Thm_PI_WGL_LTF_constant_weighted_homogeneous
import Theorems.Thm_PI_WGL_LTF_sumB
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
open PI.WGL.LTF
open PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE
namespace PI.WGL.LTF
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I) (liftWt h lam sg (tupCnt I)) := by
  classical
  have hH : IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I)
      (w0r h lam sg + ∑ k, wk h (I k) (k ∈ L)) :=
    (constant_weighted_homogeneous h lam sg).mul (IsWeightedHomogeneous.prod _ _ _ (fun k _ => G_rowW h sz hsz L k (I k)))
  convert hH using 1
  funext a
  obtain ⟨av, hav⟩ := a
  simp only [Pi.add_apply, Finset.sum_apply, wk, constant_weight_apply, Pi.single_apply, ite_apply, Pi.zero_apply,
    Finset.sum_add_distrib, liftWt]
  by_cases ha : av < n
  · have hn : 0 < n := by omega
    rw [dif_pos ha, dif_pos (by omega), dif_pos hn, if_pos ha, if_neg (by omega)]
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : (⟨av, hav⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ := fun e => by rw [Fin.mk.injEq] at e; omega
      simp [hne]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) =
        tupCnt I ⟨av, ha⟩ := by
      simp only [tupCnt, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro q _
      have : ((⟨av, hav⟩ : Fin N) = eRow h (I k q)) ↔ (I k q = ⟨av, ha⟩) := by
        simp only [eRow, Fin.ext_iff]; exact eq_comm
      by_cases hq : I k q = ⟨av, ha⟩
      · rw [if_pos (this.2 hq), if_pos hq]
      · rw [if_neg (fun e => hq (this.1 e)), if_neg hq]
    rw [hS1, hS2]
    have e3 := aLast_val h lam sg hI hn
    have e4 := sg_detShift sg hn
    have e5 := lam_detShift h lam
    omega
  · have hav' : av = n := by omega
    simp only [dif_neg ha, if_neg ha, if_pos hav', mul_zero, mul_one]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro q _
      rw [if_neg]
      intro e
      simp only [eRow, Fin.ext_iff] at e
      have := (I k q).2
      omega
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) =
        L.card := by
      rw [Finset.sum_congr rfl (g := fun k => if k ∈ L then 1 else 0)]
      · rw [← Finset.card_filter]; congr 1; ext k; simp
      · intro k _
        rw [if_pos (Fin.ext (by simp; omega))]
    rw [hS1, hS2, cardL h lam sg sz hsz hshape L hL]
    have hsplit : (∑ i : Fin n, (bb h lam sg i).toNat) =
        (∑ i : Fin n, if i.1 = 0 then (bb h lam sg i).toNat else 0) +
          ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat) 0] at hsplit
    have e6 := sumB h lam sg hI
    unfold dLast
    split_ifs at hsplit ⊢ with h1 h2 <;> omega
end PI.WGL.LTF
