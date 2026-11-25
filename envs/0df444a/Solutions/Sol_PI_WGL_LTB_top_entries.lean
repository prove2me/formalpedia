-- Prove2me | solution 1 for PI.WGL.LTB.top_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:20.26596+00:00
-- url     : https://prove2.me/submissions/10dfebbb-e6fc-4aba-ae0d-4db1df1e6eff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_sum_cnt_lt
import Theorems.Thm_PI_WGL_LTB_sum_shape_lt
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


section
noncomputable section
namespace PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
private theorem card_filter_fin_val_lt' {n c : ℕ} (hc : c ≤ n) :
    (Finset.univ.filter fun a : Fin n => a.1 < c).card = c := by
  have e : (Finset.univ.filter fun a : Fin n => a.1 < c).card = (Finset.range c).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      simpa using ha
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      have hb' : b < c := by simpa using hb
      exact ⟨⟨b, by omega⟩, by simpa using hb', rfl⟩
  rw [e, Finset.card_range]
end PI.WGL.LTB
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hc : tupCnt J = shapeDeg sz) : ∀ k p, (J k p).1 < sz k := by
  intro k p
  have key : ∀ t, t ≤ n → ∀ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = min t (sz k) := by
    intro t ht
    have hle : ∀ k ∈ Finset.univ, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card ≤ min t (sz k) := by
      intro k _
      refine le_min ?_ ?_
      · calc _ ≤ (Finset.univ.filter fun a : Fin n => a.1 < t).card :=
              Finset.card_le_card_of_injOn (J k) (by intro p hp; simpa using hp)
                (by intro a _ b _ hab; exact hinj k hab)
          _ = t := card_filter_fin_val_lt' ht
      · exact (Finset.card_filter_le _ _).trans (by simp)
    have hsum : ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = ∑ k, min t (sz k) := by
      rw [sum_cnt_lt J t, hc, sum_shape_lt sz hsz t ht]
    exact fun k => (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_univ _)
  have h1 := key (sz k) (hsz k) k
  rw [min_self] at h1
  have h2 : (Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h1]
    simp
  have h3 : p ∈ Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k := by
    rw [h2]
    exact Finset.mem_univ _
  simpa using h3
end PI.WGL.LTB
