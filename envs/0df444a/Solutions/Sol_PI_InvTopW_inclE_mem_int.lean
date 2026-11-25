-- Prove2me | solution 1 for PI.InvTopW.inclE_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:30.003878+00:00
-- url     : https://prove2.me/submissions/52227dd8-9bd1-4b46-8703-bfae4ebc72f8

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.InvTopW
theorem _root_.solution (x : E) (hx : x ∈ Formalism.UG.intOE E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x ∈ Formalism.MainNotions.S.IntAf F E := by
  first
  | exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
  | (unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt Formalism.UG.inclE
     exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩))
end PI.InvTopW
