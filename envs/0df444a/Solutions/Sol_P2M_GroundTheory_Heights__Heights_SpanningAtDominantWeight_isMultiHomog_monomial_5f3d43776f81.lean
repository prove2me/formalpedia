-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:51.026795+00:00
-- url     : https://prove2.me/submissions/a55d7b7e-d8a4-4124-88c0-7faea888760f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock

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
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution (μ : Coord n →₀ ℕ) (d : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k) :
    Geo.IsMultiHomog (ι := blockIdx n) (monomial μ (1 : ℤ)) d := by
  classical
  intro m hm k
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  exact hμ k
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
