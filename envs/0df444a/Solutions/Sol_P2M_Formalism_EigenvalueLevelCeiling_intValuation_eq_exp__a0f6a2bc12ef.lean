-- Prove2me | solution 1 for P2M_Formalism_EigenvalueLevelCeiling_intValuation_eq_exp__a0f6a2bc12ef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:32.16148+00:00
-- url     : https://prove2.me/submissions/94a6f547-cdb6-4bf0-9417-b459a278062e

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vw_coe_eq_count_factors_span_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count
      (Associates.mk (Ideal.span {x} : Ideal (𝓞 K))).factors : ℤ) := by
  have hspan : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.count_coe K w hspan, FractionalIdeal.coeIdeal_span_singleton]
end SlopeTestRemainingChoices
end Formalism.EigenvalueLevelCeiling
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by
  rw [vw_coe_eq_count_factors_span_of_ne_zero w x hx, IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hx]
end Formalism.EigenvalueLevelCeiling
