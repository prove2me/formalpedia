-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.exp_noncompactPart_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:48.894858+00:00
-- url     : https://prove2.me/submissions/b86d0f3f-7a5c-4080-9043-a68e62790547

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_isHermitian_of_mem_noncompactPart__f516412af8b5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : (NormedSpace.exp X).PosDef := by
  have hH : Xᴴ = X := isHermitian_of_mem_noncompactPart' hX
  have hYH : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by
    rw [Matrix.conjTranspose_smul, hH]
    norm_num
  have hsplit : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℂ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℂ) • X) := by
    rw [← Matrix.exp_conjTranspose, hYH, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  rw [hsplit]
  apply Matrix.PosDef.conjTranspose_mul_self
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _)
end ReciprocityTheory.ChartRestriction.DS.S7
