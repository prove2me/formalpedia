-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.sHom_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:09.599218+00:00
-- url     : https://prove2.me/submissions/eabf109b-acdb-4aee-ba45-8a32673c9f88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_sum_embedding_int
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tau_apply
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tau_int
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_int_of_inclE_mem
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_sHom_coe
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
theorem _root_.solution (I : AutInst) (x : I.E)
    (hx : Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E) : ∃ n : ℤ, sHom I x = n := by
  have := I.cm.totReal
  obtain ⟨d, hd⟩ := int_of_inclE_mem (tau I.cm.fixed) (tau_int I.cm.fixed) x hx
  obtain ⟨n, hn⟩ := sum_embedding_int I.F d
  refine ⟨n, ?_⟩
  apply Complex.ofReal_injective
  have h2 : ∀ v, I.φ v x + star (I.φ v x) = v.embedding (algebraMap (𝓞 I.F) I.F d) := by
    intro v
    rw [hd, ← I.φ_over, tau_apply, map_add, I.cm.cmUnram.2.1 (I.φ v) x]
    rfl
  rw [sHom_coe, Finset.sum_congr rfl (fun v _ => h2 v), hn]
  simp
end PI.ScPsiExists.UnitaryGroupMassFormula
