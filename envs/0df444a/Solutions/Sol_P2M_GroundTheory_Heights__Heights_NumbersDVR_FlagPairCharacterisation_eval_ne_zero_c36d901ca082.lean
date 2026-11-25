-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_eval_ne_zero_c36d901ca082
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:06.90591+00:00
-- url     : https://prove2.me/submissions/1f2ea6c5-b5d7-4ed4-8c85-0194b7231029

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_pointConeMap_of_isMultiHomog_4fe633b4dcd6


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
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type*}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    [DecidableEq K] {b : K → ℤ} {f g : MRing ι O}
    (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (pointIdeal O y) b f g) : aeval y g ≠ 0 := by
  obtain ⟨⟨α, β, -, hβ, -⟩, -, hg, -⟩ := h
  intro h0
  apply hg
  rw [pointIdeal, RingHom.mem_ker, FlagTypings.pointConeMap_of_isMultiHomog y hβ, h0, map_zero,
    zero_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
