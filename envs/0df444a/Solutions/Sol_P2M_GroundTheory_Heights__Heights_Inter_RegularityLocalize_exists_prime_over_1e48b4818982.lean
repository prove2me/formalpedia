-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalize_exists_prime_over_1e48b4818982
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:07:51.3708+00:00
-- url     : https://prove2.me/submissions/99708252-e2c9-4b95-8b0b-27ceb35f3f93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisRest
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arithVarZero_56f17dda19d2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityLocalize
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hW : IsClosedPt W) :
    ∃ p : ℤ, Prime p ∧ ∀ k : ℤ, C k ∈ W ↔ p ∣ k := by
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  have : W.IsPrime := hW.1.1
  have : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.IsPrime.comap _
  refine ⟨_, Submodule.IsPrincipal.prime_generator_of_isPrime _ hvert, fun k => ?_⟩
  rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap]
end RegularityLocalize
end GroundTheory.Heights₂.Heights.Inter
