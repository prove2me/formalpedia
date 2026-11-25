-- Prove2me | solution 1 for PI.ScRefExists.GlueA.incl_mem_Lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:25:11.131906+00:00
-- url     : https://prove2.me/submissions/245c46db-7eb2-455f-aaa9-0b126bad26ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight

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
theorem _root_.solution {x : Fin I.n → I.E} (hx : x ∈ I.L) : incl I x ∈ I.Lf := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
end PI.ScRefExists.GlueA
