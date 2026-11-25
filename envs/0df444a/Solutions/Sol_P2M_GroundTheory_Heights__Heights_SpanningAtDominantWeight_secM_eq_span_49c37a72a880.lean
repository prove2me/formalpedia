-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_secM_eq_span_49c37a72a880
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:20.02439+00:00
-- url     : https://prove2.me/submissions/dcd9664e-2cbc-4796-8d17-5f628c8fd14e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81

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
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) :
    Geo.secM (ι := blockIdx n) y d = (Submodule.span ℤ (monomialValues y d)).toAddSubgroup := by
  unfold Geo.secM
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨g, hg, rfl⟩
    rw [g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm ↦ ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hg m hm, rfl⟩)
  · rw [Submodule.span_le]
    rintro s ⟨μ, hμ, rfl⟩
    exact Submodule.subset_span ⟨monomial μ 1, isMultiHomog_monomial μ d hμ, aeval_monomial_one y μ⟩
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
