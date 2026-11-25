-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_OEv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:04.221154+00:00
-- url     : https://prove2.me/submissions/e738855c-217d-4fb4-8dd5-47e9318b6354

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

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
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (p : Fv F v ⊗[F] E) : p ∈ OEv (E := E) v ↔ p ∈ DiffLoc_P (E := E) v := by
  have h : (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ =
      inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E) := by
    ext y; simp
  unfold OEv DiffLoc_P DiffLoc_psi
  rw [h]
  rfl
end PI.LocFramePrimWork
