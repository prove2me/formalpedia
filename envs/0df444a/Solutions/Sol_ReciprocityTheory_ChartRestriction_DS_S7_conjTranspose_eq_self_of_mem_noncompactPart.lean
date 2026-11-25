-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.conjTranspose_eq_self_of_mem_noncompactPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:03.996521+00:00
-- url     : https://prove2.me/submissions/3f1dcaae-5a43-42f3-abc9-d5413aacf214

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum

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
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) : Yᴴ = Y := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    split_ifs <;> norm_num
  have h1 : Yᴴ * Jm ε = Y * Jm ε := by
    rw [hY.2]
    exact eq_neg_of_add_eq_zero_left hY.1
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Y * Jm ε * Jm ε := by rw [h1]
    _ = Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
