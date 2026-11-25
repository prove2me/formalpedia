-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalDivisorChartGeneric_ringKrullDim_le_of_injective_isIntegral_893eb26f2a3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:11.188112+00:00
-- url     : https://prove2.me/submissions/5baeddd9-9f0c-42e7-88f3-fa29a0cc4843

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDivisorChartGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDivisorChartGeneric
namespace GroundTheory.Heights₂.Heights.NormalDivisorChartGeneric
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])
end GroundTheory.Heights₂.Heights.NormalDivisorChartGeneric
