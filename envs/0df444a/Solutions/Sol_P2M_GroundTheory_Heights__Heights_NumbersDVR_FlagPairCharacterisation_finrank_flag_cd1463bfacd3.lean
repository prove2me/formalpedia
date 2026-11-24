-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_finrank_flag_cd1463bfacd3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:43.118876+00:00
-- url     : https://prove2.me/submissions/0e5a171e-13cc-4e52-9131-c6abb72cf7d4

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
theorem _root_.solution (w : Module.Basis (Fin N) Ω E) (i : Fin (N + 1)) :
    Module.finrank Ω (Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})) = i := by
  classical
  have hli : LinearIndependent Ω (fun x : {j : Fin N | (j : ℕ) < i} => w x) :=
    w.linearIndependent.comp _ Subtype.val_injective
  rw [Set.image_eq_range, finrank_span_eq_card hli]
  simp only [Fintype.card_subtype, Set.mem_ofPred_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Nat.lt_succ_iff.mp i.isLt)
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
