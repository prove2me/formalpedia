-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.fr_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:10.646788+00:00
-- url     : https://prove2.me/submissions/03cc45a2-4aa6-4c4e-b03b-43f0347fdb18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_real_emb
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_add_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_smul_left
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
open NumberField Matrix Formalism.UG PI.InHHClassFin Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (hS : DefiniteCompl I S) : Disjoint (Submodule.span I.E S) (frW I S) := by
  rw [Submodule.disjoint_def]
  intro x hxS hxW
  by_contra hx0
  have key : ∀ z ∈ Submodule.span I.E S, hform (starRingEnd I.E) I.J z x = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hxW z hz
    | zero => simp [hform]
    | add u v _ _ hu hv => rw [hform_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [hform_smul_left, hu, mul_zero]
  obtain ⟨ι⟩ := fr_real_emb I
  rcases hS ι with h | h
  · obtain ⟨a, ha, hpos⟩ := h x hx0 (fun s hs => hxW s hs)
    rw [key x hxS] at ha
    have ha0 : a = 0 := (algebraMap I.F I.E).injective (by rw [ha, map_zero])
    rw [ha0, map_zero] at hpos
    exact lt_irrefl _ hpos
  · obtain ⟨a, ha, hneg⟩ := h x hx0 (fun s hs => hxW s hs)
    rw [key x hxS] at ha
    have ha0 : a = 0 := (algebraMap I.F I.E).injective (by rw [ha, map_zero])
    rw [ha0, map_zero] at hneg
    exact lt_irrefl _ hneg
end PI.UnitaryGroupMassFormula.InHHClassFin
