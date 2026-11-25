-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.LcV_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:30.033962+00:00
-- url     : https://prove2.me/submissions/6170e264-b13f-46f6-88cc-b23078341154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_stdBasis_reprV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {Q : Type} [Fintype Q] [DecidableEq Q] (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (LcV (Q := Q) g) = g.det ^ Fintype.card Q := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) Q)]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) Q) (Matrix.stdBasis ℂ (Fin n) Q) (LcV (Q := Q) g) =
      Matrix.kroneckerMap (fun x1 x2 => x1 * x2) g (1 : Matrix Q Q ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_reprV, Matrix.stdBasis_eq_single]
    simp [LcV, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Ne.symm hlj]
  rw [h, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
