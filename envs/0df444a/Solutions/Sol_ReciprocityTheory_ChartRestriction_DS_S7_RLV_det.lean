-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.RLV_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:20.865098+00:00
-- url     : https://prove2.me/submissions/eb215d97-420e-43bc-a409-213cf969d324

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_normSq_detVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_LcV_det

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
theorem _root_.solution {Q : Type} [Fintype Q] [DecidableEq Q] {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : LinearMap.det (RLV (Q := Q) g) = 1 := by
  have h1 : RLV (Q := Q) g = ((ReV n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] REV n Q) ∘ₗ
      ((LcV (Q := Q) g).restrictScalars ℝ) ∘ₗ
      (((ReV n Q).symm).symm : REV n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ) := rfl
  rw [h1, LinearMap.det_conj, LinearMap.det_restrictScalars, LcV_det, Algebra.norm_complex_apply, map_pow,
    normSq_detVG hg, one_pow]
end ReciprocityTheory.ChartRestriction.DS.S7
