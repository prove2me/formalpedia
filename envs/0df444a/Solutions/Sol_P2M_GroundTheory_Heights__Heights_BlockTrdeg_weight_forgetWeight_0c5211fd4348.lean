-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_weight_forgetWeight_0c5211fd4348
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:42.261835+00:00
-- url     : https://prove2.me/submissions/86df545d-269f-40dd-bcc2-82286fce4013

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
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (κ : K → K') (m : (Σ k', ι' k') →₀ ℕ) (k : Forgotten κ) :
    Finsupp.weight (forgetWeight (ι' := ι') κ) m k = ∑ i, m ⟨k.1, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k.1]
  · simp [forgetWeight]
  · intro b _ hb
    simp [forgetWeight, hb]
  · simp
end GroundTheory.Heights₂.Heights.BlockTrdeg
