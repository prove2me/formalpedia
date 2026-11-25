-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_eq_74c67895a811
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:08.552697+00:00
-- url     : https://prove2.me/submissions/a7bea265-d4a8-49bf-a156-9e9026cc7a99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3

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
theorem _root_.solution (w : Module.Basis (Fin N) Ω E) {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) (hmem : ∀ j, w j ∈ Vs j.succ) (i : Fin (N + 1)) :
    Vs i = Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
  have : FiniteDimensional Ω E := Module.Finite.of_basis w
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_flag, dim])
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mono (Fin.le_def.mpr (by simpa using hj)) (hmem j)
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
