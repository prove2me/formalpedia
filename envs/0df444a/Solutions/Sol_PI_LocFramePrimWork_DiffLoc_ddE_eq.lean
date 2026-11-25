-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_ddE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:24.929497+00:00
-- url     : https://prove2.me/submissions/08c75730-ba96-43dd-8822-4b33d5723130

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
theorem _root_.solution : ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
    (Submodule.span (𝓞 E) ((fun d : 𝓞 F => algebraMap F E (d : F)) ''
      (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) : Set E) := by
  show (((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) : Set E) = _
  unfold ddE
  rw [FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule, Ideal.map, Ideal.span, Submodule.map_span,
    Set.image_image]
  rfl
end PI.LocFramePrimWork
