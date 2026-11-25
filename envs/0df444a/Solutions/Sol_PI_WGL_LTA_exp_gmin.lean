-- Prove2me | solution 1 for PI.WGL.LTA.exp_gmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:58.245517+00:00
-- url     : https://prove2.me/submissions/7e500662-e9ce-441b-bbce-daf61e738547

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Theorems.Thm_PI_WGL_LTA_rowGen_gmin
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
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL.LTA
theorem _root_.solution {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (κ : Fin m → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (e ∘ ρ) κ) := by
  intro a b ρ
  beta_reduce
  rw [rowGen_gmin]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (∀ p ∈ S, (e ∘ ρ) p = e b) ↔ (∀ p ∈ S, ρ p = b) := by
    simp only [Function.comp_apply, he.eq_iff]
  have h2 : upd (e ∘ ρ) S (e a) = e ∘ upd ρ S a := by
    funext p
    simp only [upd, Function.comp_apply]
    split_ifs <;> rfl
  by_cases hc : ∀ p ∈ S, ρ p = b
  · rw [if_pos hc, if_pos (h1.mpr hc), h2]
  · rw [if_neg hc, if_neg (fun h => hc (h1.mp h))]
end PI.WGL.LTA
