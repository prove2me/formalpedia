-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_isWeightedHomogeneous_rename_3526478ad33d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:40.620912+00:00
-- url     : https://prove2.me/submissions/81f38f7e-8bef-4524-8ee1-800f09ac2510

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
omit [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : ∀ p, (v p).1 ∈ Set.range κ) (g : MvPolynomial (Σ k, ι k) ℤ) :
    IsWeightedHomogeneous (forgetWeight κ) (rename v g) 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact isWeightedHomogeneous_C _ _
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p q hp =>
    rw [map_mul, rename_X]
    have h0 : forgetWeight κ (v q) = 0 := by
      funext k
      simp only [forgetWeight, Pi.zero_apply]
      rw [if_neg]
      intro h
      exact k.2 (h ▸ hv q)
    have := hp.mul (isWeightedHomogeneous_X ℤ (forgetWeight κ) (v q))
    rwa [h0, add_zero] at this
end GroundTheory.Heights₂.Heights.BlockTrdeg
