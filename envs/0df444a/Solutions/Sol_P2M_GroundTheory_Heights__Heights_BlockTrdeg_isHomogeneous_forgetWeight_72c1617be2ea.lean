-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_isHomogeneous_forgetWeight_72c1617be2ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:13.445099+00:00
-- url     : https://prove2.me/submissions/b45345d5-cd34-4df0-bff5-3eee822f9476

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_weight_forgetWeight_0c5211fd4348

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (κ : K → K') {P : Ideal (MRing ι')} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (forgetWeight (ι' := ι') κ)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := hS x hx
  refine ⟨fun k ↦ a k.1, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_⟩
  intro d hd
  funext k
  rw [weight_forgetWeight]
  exact ha d (mem_support_iff.mpr hd) k.1
end GroundTheory.Heights₂.Heights.BlockTrdeg
