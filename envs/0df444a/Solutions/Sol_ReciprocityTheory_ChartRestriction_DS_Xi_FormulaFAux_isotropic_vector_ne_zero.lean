-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.isotropic_vector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:04.876914+00:00
-- url     : https://prove2.me/submissions/6dcd6cce-2ce8-4c98-b516-5332364e2a8d

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
theorem _root_.solution (k r' : ℕ) : eI k (1 + r') (a0 r') ≠ esI k (1 + r') (a0 r') := by
  intro h
  have h' := congrArg Fin.val h
  simp only [eI, esI, a0, Fin.val_mk] at h'
  omega
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
