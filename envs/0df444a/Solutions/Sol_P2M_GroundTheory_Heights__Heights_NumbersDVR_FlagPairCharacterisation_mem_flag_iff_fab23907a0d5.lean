-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_mem_flag_iff_fab23907a0d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:18.338794+00:00
-- url     : https://prove2.me/submissions/d9fb8a49-1931-4141-99df-fac737b3baad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
theorem _root_.solution (w : Module.Basis (Fin N) Ω E) (n : ℕ) (x : E) :
    x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < n}) ↔ ∀ j : Fin N, n ≤ (j : ℕ) → w.repr x j = 0 := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    exact absurd (h (Finsupp.mem_support_iff.mpr hne)) (by simpa using hj)
  · intro h j hj
    by_contra hne
    exact Finsupp.mem_support_iff.mp hj (h j (by simpa using hne))
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
