-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.shifted_mem_weightSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:56.865131+00:00
-- url     : https://prove2.me/submissions/07f147a8-0d24-4369-a087-97a65bfd654e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector

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
theorem _root_.solution (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) : inWb k r' (fun q => z (sh q)) := by
  unfold inWb at hz ⊢
  intro i hi
  have := i.isLt
  exact hz (sh i) (by simp only [sh, Fin.val_mk]; omega)
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
