-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:17.391173+00:00
-- url     : https://prove2.me/submissions/52281a34-e7c9-4e0d-8dde-266f14b18df3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_dot_bvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_mv_bvec


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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : herm H (bvec i) (bvec j) = H j i := by
  unfold herm; rw [dot_bvec, mv_bvec]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
