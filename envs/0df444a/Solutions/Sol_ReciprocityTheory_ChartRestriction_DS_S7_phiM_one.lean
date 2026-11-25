-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.phiM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:36.558799+00:00
-- url     : https://prove2.me/submissions/5bf27064-224d-4eb3-a924-55dcc8ca8d0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts

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
theorem _root_.solution (μ : Fin n → ℤ) : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold PhiM
  have h1 : ∀ i : Fin n, lead ((i : ℕ) + 1) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro i
    unfold lead
    rw [dif_pos (by have := i.2; omega), Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  simp [h1]
end ReciprocityTheory.ChartRestriction.DS.S7
