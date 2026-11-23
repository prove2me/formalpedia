-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_ReductionFirst_InS_star__e6df83696a45
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:38.582824+00:00
-- url     : https://prove2.me/submissions/0cb4da95-4d5b-475d-8f48-1a3cb5cc5ab9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_cO_coe
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_cO_mem_Tw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ReductionFirst
namespace InS
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : InS w x) : InS w (star x) := by
  obtain ⟨s, hs, r, hr⟩ := h
  refine ⟨cO K s, cO_mem_Tw hs, cO K r, ?_⟩
  rw [cO_coe, cO_coe, ← hr, star_mul']
end InS
end Formalism.DivisionValues.ReductionFirst
