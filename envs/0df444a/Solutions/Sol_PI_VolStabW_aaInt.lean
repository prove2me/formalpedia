-- Prove2me | solution 1 for PI.VolStabW.aaInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:10.488882+00:00
-- url     : https://prove2.me/submissions/dedb110a-d83b-4499-9b36-9671738f024b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH

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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
variable {b v}
namespace PI.VolStabW
theorem _root_.solution (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  refine Filter.eventually_cofinite.2 (h.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  rw [not_le] at hv
  show 1 < v.valuation F x
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hv
end PI.VolStabW
