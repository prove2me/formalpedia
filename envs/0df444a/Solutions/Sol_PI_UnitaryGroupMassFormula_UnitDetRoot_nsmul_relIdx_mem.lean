-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:20.190835+00:00
-- url     : https://prove2.me/submissions/12a35727-e29a-4e1c-927c-b6c74104181a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {V : Type*} [AddCommGroup V] (H K : AddSubgroup V) {x : V} (hx : x ∈ K) :
    (H.relIndex K) • x ∈ H := by
  have h := (H.addSubgroupOf K).nsmul_index_mem ⟨x, hx⟩
  rw [AddSubgroup.relIndex]
  simpa [AddSubgroup.mem_addSubgroupOf] using h
end PI.UnitaryGroupMassFormula.UnitDetRoot
