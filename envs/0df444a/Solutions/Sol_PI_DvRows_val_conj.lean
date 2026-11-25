-- Prove2me | solution 1 for PI.DvRows.val_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:39.963748+00:00
-- url     : https://prove2.me/submissions/09718a52-a749-4505-9562-e4a88912aa0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_intVal_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (conjW w).valuation K x = w.valuation K (star x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have e : star (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
      algebraMap (𝓞 K) K (starO K a) / algebraMap (𝓞 K) K (starO K b) := by
    rw [← starRingEnd_apply, map_div₀, starRingEnd_apply, starRingEnd_apply]
    rfl
  rw [e, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intVal_conj, intVal_conj]
end PI.DvRows
