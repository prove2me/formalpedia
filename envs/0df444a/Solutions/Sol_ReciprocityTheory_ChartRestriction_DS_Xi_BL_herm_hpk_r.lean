-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_hpk_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:41.696801+00:00
-- url     : https://prove2.me/submissions/d52e76cd-3b40-4eb3-8fab-b888b511e424

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_mul


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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v (Hpk k r *ᵥ w) = star w ⬝ᵥ v := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, hpk_conjT, mulVec_mulVec, hpk_mul, one_mulVec]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
