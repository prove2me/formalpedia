-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.lv_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:07.813146+00:00
-- url     : https://prove2.me/submissions/19c6dd98-fda0-4738-82c9-269b0f74fa48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec

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
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) : liftVec k 1 r' v (sh q) = v q := by
  unfold liftVec; rw [dif_pos (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
