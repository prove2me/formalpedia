-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.lift_kills_last_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:06.768919+00:00
-- url     : https://prove2.me/submissions/566aa162-b3d7-47cc-87d9-1f3e67e8ebaa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula

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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (esI k (1 + r') (a0 r')) = 0 := by
  unfold liftVec
  rw [dif_neg (by simp only [esI, a0, Fin.val_mk]; omega)]
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
