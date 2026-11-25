-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:48.761298+00:00
-- url     : https://prove2.me/submissions/330a673f-3cc8-4e65-86fc-a6760d0c3633

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_psiEinf_eq
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_sHom_int
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
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution : Target := by
  intro I
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let N : AddSubgroup (I.E ⊗[I.F] Af I.F) := (IntAf I.F I.E).toAddSubgroup
  let π : I.E ⊗[I.F] Af I.F →+ (I.E ⊗[I.F] Af I.F) ⧸ N := QuotientAddGroup.mk' N
  let j : I.E →+ (I.E ⊗[I.F] Af I.F) ⧸ N :=
    π.comp (Formalism.UG.inclE (F := I.F) (Af I.F)).toAddMonoidHom
  let sb : I.E →+ AddCircle (1 : ℝ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (sHom I)
  have hker : j.ker ≤ sb.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    have hx' : Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E :=
      (QuotientAddGroup.eq_zero_iff _).1 hx
    obtain ⟨n, hn⟩ := sHom_int I x hx'
    show ((sHom I x : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [hn, AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩
  let g0 : I.E ⧸ j.ker →+ AddCircle (1 : ℝ) := QuotientAddGroup.lift j.ker sb hker
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g0
  have hj : ∀ x, h (j x) = sb x := by
    intro x
    have := DFunLike.congr_fun hh (x : I.E ⧸ j.ker)
    simpa [g0] using this
  refine ⟨fun z => ((AddCircle.toCircle (-(h (π z))) : Circle) : ℂ), ?_, ?_, ?_⟩
  · intro z w
    simp only [map_add, neg_add, AddCircle.toCircle_add, Circle.coe_mul]
  · intro z hz
    have hz0 : π z = 0 := (QuotientAddGroup.eq_zero_iff z).2 hz
    simp only [hz0, map_zero, neg_zero]
    rw [← AddCircle.coe_zero, AddCircle.toCircle_apply_mk]
    simp
  · intro x
    show ((AddCircle.toCircle (-(h (j x)))) : ℂ) * psiEinf I x = 1
    rw [hj, psiEinf_eq]
    show ((AddCircle.toCircle (-((sHom I x : ℝ) : AddCircle (1 : ℝ)))) : ℂ) * _ = 1
    rw [← AddCircle.coe_neg, AddCircle.toCircle_apply_mk, Circle.coe_exp, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
end PI.ScPsiExists.UnitaryGroupMassFormula
