-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_component_mul_a84826e9810b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:21.326698+00:00
-- url     : https://prove2.me/submissions/6acecaab-3487-40e1-aa8c-78179387379d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb

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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
theorem _root_.solution {f : MRing ι F} {s : K → ℕ} (hf : IsMultiHomog f s) (c : MRing ι F)
    (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (f * c) =
      if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := c) n hf
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.FiltrationStepHilb
