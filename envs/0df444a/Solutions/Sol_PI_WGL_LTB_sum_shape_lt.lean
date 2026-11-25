-- Prove2me | solution 1 for PI.WGL.LTB.sum_shape_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:08:42.645481+00:00
-- url     : https://prove2.me/submissions/7a836ec6-9cfb-4970-836a-ce6ad9be61fd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
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
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (t : ℕ) (ht : t ≤ n) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), shapeDeg sz a = ∑ k, min t (sz k) := by
  unfold shapeDeg
  have e : ∀ k : Fin K, min t (sz k) = (Finset.univ.filter fun a : Fin n => a.1 < t ∧ a.1 < sz k).card := by
    intro k
    rw [← card_filter_fin_val_lt' (n := n) (c := min t (sz k)) (le_trans (min_le_left _ _) ht)]
    apply congrArg Finset.card
    ext a
    simp [lt_min_iff]
  simp only [e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : a.1 < t <;> simp [ha]
end PI.WGL.LTB
