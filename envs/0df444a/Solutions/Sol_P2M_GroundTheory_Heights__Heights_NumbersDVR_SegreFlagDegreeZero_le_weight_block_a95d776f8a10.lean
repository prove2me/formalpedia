-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_le_weight_block_a95d776f8a10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:23.31327+00:00
-- url     : https://prove2.me/submissions/18a42290-380d-490a-9a24-bcfe754fd74d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalEqOfVdeg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero
theorem _root_.solution {κ : Type} [DecidableEq κ] {τ : κ → Type} (c : (Σ o, τ o) →₀ ℕ) {p : Σ o, τ o}
    (hp : p ∈ c.support) : c p ≤ Finsupp.weight (blockWeight τ) c p.1 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  refine le_trans (le_of_eq ?_)
    (Finset.single_le_sum (f := fun x => (c x • blockWeight τ x) p.1) (fun _ _ => Nat.zero_le _) hp)
  simp [blockWeight]
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero
