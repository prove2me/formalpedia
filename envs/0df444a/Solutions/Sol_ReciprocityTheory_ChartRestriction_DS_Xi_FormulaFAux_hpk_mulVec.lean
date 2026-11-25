-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.hpk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:53.643544+00:00
-- url     : https://prove2.me/submissions/114af66c-dc02-44d1-803e-d9168c523f13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hpk_apply

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
theorem _root_.solution (k r : ℕ) (w : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ w) i = (if i.val = r + k then -1 else 1) * w (sg k r i) := by
  simp [mulVec, dotProduct, hpk_apply]
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
