-- Prove2me | solution 1 for PI.ScRefExists.GlueA.smul_mem_Lf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:25:18.810288+00:00
-- url     : https://prove2.me/submissions/81bb5817-f707-4d6d-8511-ac8ee9006412

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
theorem _root_.solution {c : (I.E ⊗[I.F] Af I.F)} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ I.Lf) : c • x ∈ I.Lf := Submodule.smul_mem _ (⟨c, hc⟩ : IntAf I.F I.E) hx
end PI.ScRefExists.GlueA
