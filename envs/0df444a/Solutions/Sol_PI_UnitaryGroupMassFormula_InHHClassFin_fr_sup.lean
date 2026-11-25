-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.fr_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:23.023018+00:00
-- url     : https://prove2.me/submissions/1ca07ddc-676f-40b2-83f4-c3b4a613b950

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_disj
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_hform_sum_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_add_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_smul_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_smul_right
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
theorem _root_.solution (hS : DefiniteCompl I S) : Submodule.span I.E S ⊔ frW I S = ⊤ := by
  classical
  set V := Submodule.span I.E S with hV
  let b := Module.finBasis I.E V
  let T : (Fin I.n → I.E) →ₗ[I.E] (Fin (Module.finrank I.E V) → I.E) :=
    { toFun := fun y k => hform (starRingEnd I.E) I.J (b k : Fin I.n → I.E) y
      map_add' := by intro x y; funext k; simp [hform_add_right]
      map_smul' := by intro c x; funext k; simp [hform_smul_right] }

  have hker : LinearMap.ker T ≤ frW I S := by
    intro y hy s hs
    have hy' : ∀ k, hform (starRingEnd I.E) I.J (b k : Fin I.n → I.E) y = 0 :=
      fun k => congrFun (LinearMap.mem_ker.mp hy) k
    have hexp : ∑ k, b.repr ⟨s, Submodule.subset_span hs⟩ k • (b k : Fin I.n → I.E) = s := by
      have := congrArg Subtype.val (b.sum_repr ⟨s, Submodule.subset_span hs⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this
    rw [← hexp, fr_hform_sum_left]
    simp [hform_smul_left, hy']
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hr : Module.finrank I.E (LinearMap.range T) ≤ Module.finrank I.E V := by
    have := Submodule.finrank_le (LinearMap.range T)
    simpa using this
  have hW : Module.finrank I.E (LinearMap.ker T) ≤ Module.finrank I.E (frW I S) :=
    Submodule.finrank_mono hker
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V (frW I S)
  have hinf : V ⊓ frW I S = ⊥ := disjoint_iff.mp (fr_disj hS)
  rw [hinf, finrank_bot, add_zero] at hsup
  have hn : Module.finrank I.E (Fin I.n → I.E) = I.n := Module.finrank_fin_fun I.E
  have hle := Submodule.finrank_le (V ⊔ frW I S)
  apply Submodule.eq_top_of_finrank_eq
  omega
end PI.UnitaryGroupMassFormula.InHHClassFin
