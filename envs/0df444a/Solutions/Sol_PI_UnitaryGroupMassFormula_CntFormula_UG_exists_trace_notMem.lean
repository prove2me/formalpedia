-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_trace_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:19.21322+00:00
-- url     : https://prove2.me/submissions/22bb3193-3073-49eb-9135-acec6938ec2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_PairUnitLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsTraceNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_sub_conjO_notMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ l : 𝓞 K, l + conjO K l ∉ p := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  by_cases h2 : (2 : 𝓞 K) ∈ p
  · refine ⟨θ, fun h => hθ ?_⟩
    have e : θ - conjO K θ = (θ + conjO K θ) - 2 * conjO K θ := by ring
    rw [e]
    exact p.sub_mem h (p.mul_mem_right _ h2)
  · refine ⟨1, ?_⟩
    rw [map_one, one_add_one_eq_two]
    exact h2
end PI.UnitaryGroupMassFormula.CntFormula.UG
