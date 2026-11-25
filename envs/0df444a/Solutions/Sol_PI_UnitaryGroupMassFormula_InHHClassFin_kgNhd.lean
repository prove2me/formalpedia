-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:41.769145+00:00
-- url     : https://prove2.me/submissions/ddf1287b-34c4-4b91-85cb-538c232e90ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_OneMemKg
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_one_mem_Kg
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
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution : KgNhd := by
  intro I g x hg
  letI := I.topf
  haveI := I.topf_group
  have hK : I.Kg g ∈ nhds (1 : I.Gf) := (I.topf_open g hg).mem_nhds (one_mem_Kg I g)
  have hc : Continuous fun h : I.Gf => x⁻¹ * h * x := by fun_prop
  have hT : {h : I.Gf | x⁻¹ * h * x ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have hK' : I.Kg g ∈ nhds (x⁻¹ * 1 * x) := by simpa using hK
    exact hc.continuousAt hK'
  obtain ⟨g', hg', hsub⟩ := I.topf_basis _ hT
  exact ⟨g', hg', fun h hh => hsub hh⟩
end PI.UnitaryGroupMassFormula.InHHClassFin
