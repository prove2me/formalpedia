-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.inR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:51:09.907524+00:00
-- url     : https://prove2.me/submissions/48aa2154-d3b3-4379-9e49-82f3e8db01a6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) {x y : Av I v} (hx : InR I v α x) (hy : InR I v α y) :
    InR I v α (x * y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  refine ⟨a * c - b * d, a * d + b * c + b * d * t, sub_mem (mul_mem ha hc) (mul_mem hb hd),
    add_mem (add_mem (mul_mem ha hd) (mul_mem hb hc)) (mul_mem (mul_mem hb hd) htO), ?_⟩
  simp only [map_sub, map_add, map_mul]
  linear_combination (incL I v b * incL I v d) * ht
end PI.UnitaryGroupMassFormula.AdIndexEq
