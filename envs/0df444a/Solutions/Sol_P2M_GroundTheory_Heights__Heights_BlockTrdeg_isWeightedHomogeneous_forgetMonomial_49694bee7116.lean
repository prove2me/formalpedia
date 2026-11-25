-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_forgetMonomial_49694bee7116
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:39.064181+00:00
-- url     : https://prove2.me/submissions/11246a08-41ce-46f5-893a-a4ffdedfd304

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg

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
omit [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1)
    (a : Forgotten κ →₀ ℕ) :
    IsWeightedHomogeneous (forgetWeight κ) (forgetMonomial κ i a) ⇑a := by
  have := IsWeightedHomogeneous.prod Finset.univ (fun k ↦ (X ⟨k.1, i k⟩ : MRing ι') ^ a k)
    (fun k ↦ a k • forgetWeight κ ⟨k.1, i k⟩)
    fun k _ ↦ (isWeightedHomogeneous_X ℤ (forgetWeight κ) _).pow (a k)
  unfold forgetMonomial
  convert this using 1
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [forgetWeight]
  · intro b _ hb
    rw [Pi.smul_apply, forgetWeight, if_neg (fun h ↦ hb (Subtype.ext h)), smul_zero]
  · simp
end GroundTheory.Heights₂.Heights.BlockTrdeg
