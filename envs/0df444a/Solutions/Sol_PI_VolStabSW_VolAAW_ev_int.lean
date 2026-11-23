-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.ev_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:19.384261+00:00
-- url     : https://prove2.me/submissions/7826f12e-691e-4459-8d01-cc68b9087402

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA

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
theorem _root_.solution (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) f ∈ (v.adicCompletionIntegers F) := by
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) f
  refine hfin.eventually_cofinite_notMem.mono fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v ((f : v.adicCompletion F)) = v.valuation F f :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  exact (this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)
end PI.VolStabSW.VolAAW
