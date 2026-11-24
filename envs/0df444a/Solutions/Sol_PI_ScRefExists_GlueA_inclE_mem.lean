-- Prove2me | solution 1 for PI.ScRefExists.GlueA.inclE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:20:10.882817+00:00
-- url     : https://prove2.me/submissions/fa75e6eb-0ae2-44aa-976a-583d00f06f4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Theorems.Thm_PI_ScRefExists_GlueA_inclE_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GlueA
theorem _root_.solution {a : I.E} (ha : a ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  rw [inclE_tmul]
  exact Subring.subset_closure (Set.mem_union_left _ ⟨⟨a, ha⟩, rfl⟩)
end PI.ScRefExists.GlueA
