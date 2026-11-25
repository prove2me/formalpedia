-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_nsmul_92370521b91e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:03.456301+00:00
-- url     : https://prove2.me/submissions/46fbf4b6-4bd6-4380-be12-1e825b1c0296

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_add_7ddf77459fd7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_monomialValues_zero_a00cab2fcc08


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) (τ : ℕ) :
    monomialValues y (τ • d) = monomialValues y d ^ τ := by
  induction τ with
  | zero => rw [zero_smul, monomialValues_zero, pow_zero, Set.singleton_one]
  | succ τ ih => rw [succ_nsmul, monomialValues_add, ih, pow_succ]
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
