-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_ratV_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:51.222342+00:00
-- url     : https://prove2.me/submissions/dc0729a9-af04-4e1e-844c-f366f30443cb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution (x : E) (y : Fin n → E) :
    inclR (F := F) (Fv F v) x • ratV (F := F) (Fv F v) y = ratV (F := F) (Fv F v) (x • y) := by
  funext i; simp [ratV, map_mul]
end PI.LocFramePrimWork
