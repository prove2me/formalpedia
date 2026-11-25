-- Prove2me | solution 1 for PI.InvTopW.algebraMap_mem_intOE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:13.382808+00:00
-- url     : https://prove2.me/submissions/4bd47d4b-ff05-4c44-81c6-f42d0baa9c92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : 𝓞 E) :
    algebraMap (𝓞 E) E a ∈ Formalism.UG.intOE E := by
  first
  | exact RingHom.mem_range_self _ a
  | exact ⟨a, rfl⟩
end PI.InvTopW
