-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.eI_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:12:59.172115+00:00
-- url     : https://prove2.me/submissions/dff147ad-85a0-460a-929e-d0803d640fd6

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
theorem _root_.solution (b : ℕ) (h : b + 1 < 1 + r') : eI k (1 + r') ⟨b + 1, h⟩ = sh (eI k r' ⟨b, by omega⟩) := by
  ext
  simp [eI, sh]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
