-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_w_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:03.630632+00:00
-- url     : https://prove2.me/submissions/90b78986-3ead-4272-9e85-80a203a7348c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_dot_bvec_r
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_bvec_w

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
variable (k n : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) (wv k n i) v = star (v (wp k n i)) := by
  unfold herm
  rw [hpk_bvec_w]
  simp only [wv]
  rw [dot_bvec_r]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
