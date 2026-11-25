-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.lift_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:49:31.542185+00:00
-- url     : https://prove2.me/submissions/e9ffa1f8-efd3-4992-9d8c-4de5b268811d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_levPos_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_lift_levPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_lift_zero

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
theorem _root_.solution (k r' : ℕ) (u v : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' u) ⬝ᵥ liftVec k 1 r' v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply]
  symm
  refine Fintype.sum_of_injective _ (levPos_inj k r') _ _ (fun p hp => ?_) (fun i => ?_)
  · rw [lift_zero _ _ v _ hp, mul_zero]
  · rw [lift_levPos, lift_levPos]
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
