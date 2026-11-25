-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:31.183608+00:00
-- url     : https://prove2.me/submissions/827bfce6-69ae-49d4-a64f-74e8ef2e9957

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
theorem _root_.solution (p : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k)
    (q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') p (sh q) = 0 := by
  have := p.isLt
  have := q.isLt
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
