-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.ev_int_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:53.495516+00:00
-- url     : https://prove2.me/submissions/8b4326f0-feb0-43f4-8af1-1b0b85e6af65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Theorems.Thm_PI_VolStabSW_VolAAW_ev_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.VolAAW
theorem _root_.solution {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) :=
  Filter.eventually_all.2 fun i => ev_int (f i)
end PI.VolStabSW.VolAAW
