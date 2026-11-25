-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hermitianForm_liftVec_firstVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:38.606975+00:00
-- url     : https://prove2.me/submissions/208130dd-4dee-45bc-8559-7dcf5047cbcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_lv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
  unfold herm
  rw [hpk_lv]
  simp [e0, bvec, dotProduct, Pi.single_apply, liftVec, eI, a0]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h1 h2 <;> first | rfl | (rw [h2] at h1; simp at h1)
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
