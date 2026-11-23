-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_frac_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:38.560804+00:00
-- url     : https://prove2.me/submissions/e84b6658-046b-4949-a2d3-b681d3f5f804

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
theorem _root_.solution (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    ∀ (o : 𝓞 E) (s : E), s ∈ (I : Set E) → (o : E) * s ∈ (I : Set E) := by
  intro o s hs
  have := (I : Submodule (𝓞 E) E).smul_mem o hs
  rwa [Algebra.smul_def] at this
end PI.LocFramePrimWork
