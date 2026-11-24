-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.mem_oLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:15:46.216919+00:00
-- url     : https://prove2.me/submissions/a4110bcf-7316-460f-863e-9a62b029b49b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
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
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {k : ℕ} (v : Fin k → E) :
    v ∈ oLat E k ↔ ∃ x : Fin k → 𝓞 E, (fun c => algebraMap (𝓞 E) E (x c)) = v := by
  unfold oLat
  first
  | (rw [LinearMap.mem_range]; rfl)
  | exact Iff.rfl
  | (simp [LinearMap.mem_range, LinearMap.compLeft]; rfl)
end PI.UnitaryGroupMassFormula.LCG
