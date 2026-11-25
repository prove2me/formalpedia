-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_ratTup_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:02.390082+00:00
-- url     : https://prove2.me/submissions/4a2e6b78-2147-4d42-ac14-50c425b91829

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
theorem _root_.solution {r : ℕ} (e : Fin r → Fin n → E) (z : Fin n → E) (a : Fin r) :
    ratTup (F := F) (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E) (Fin.castSucc a) =
      ratV (F := F) (Fv F v) (e a) := by
  funext i; simp [ratTup, ratV]
end PI.LocFramePrimWork
