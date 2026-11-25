-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_OEv_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:39.325803+00:00
-- url     : https://prove2.me/submissions/c5c624a1-fa73-4354-943d-b37e2e8ee00b

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
theorem _root_.solution (y : Fv F v ⊗[F] E)
    (hy : y ∈ Submodule.span (v.adicCompletionIntegers F)
      (inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E))) : y ∈ OEv (E := E) v := by
  have h : inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E) =
      (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ := by
    ext y; simp
  rw [h] at hy
  exact hy
end PI.LocFramePrimWork
