-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:56.301889+00:00
-- url     : https://prove2.me/submissions/3926ee4b-3f4f-4b93-99d6-17e307cba9ab

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
theorem _root_.solution : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  refine Submodule.subset_span ⟨1, Set.mem_univ _, ?_⟩
  simp [inclR, Algebra.TensorProduct.one_def]
end PI.LocFramePrimWork
