-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.star_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:03.863667+00:00
-- url     : https://prove2.me/submissions/16a6c07c-733c-45fb-920e-9cdc10d974a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ChooseW_sv_sv
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {E : Type*} [Field E] [StarRing E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution {k : ℕ} (v : Fin k → Fin n → E) (w : Fin n → E)
    (hw : sv w ∈ Submodule.span E (Set.range v)) :
    w ∈ Submodule.span E (Set.range fun a => sv (v a)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hw
  refine (Submodule.mem_span_range_iff_exists_fun E).mpr ⟨fun a => starRingEnd E (c a), ?_⟩
  rw [← sv_sv w, ← hc]
  funext j
  simp [sv, Finset.sum_apply, map_sum, map_mul]
end PI.UnitaryGroupMassFormula.LCG.ChooseW
