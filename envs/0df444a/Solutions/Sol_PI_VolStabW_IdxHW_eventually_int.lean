-- Prove2me | solution 1 for PI.VolStabW.IdxHW.eventually_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:45.998336+00:00
-- url     : https://prove2.me/submissions/83acdfe9-dab3-4ada-936f-0f7badf70368

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
namespace PI.VolStabW.IdxHW
theorem _root_.solution (x : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).eventually
end PI.VolStabW.IdxHW
