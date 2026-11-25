-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lev_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:56.780341+00:00
-- url     : https://prove2.me/submissions/de6a0e7b-6dd4-4c2e-bbd1-bfd48b0cedca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last

set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (g : Mat k r') (p : Fin (2 * (1 + r') + k + 1)) (j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g p (mp k r' j) =
      if hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then g ⟨p.val - 1, by omega⟩ j else 0 := by
  have hj := j.isLt
  simp only [ιLev, mp, Fin.ext_iff, and_false, false_and, and_true, true_and, not_false_eq_true, not_true_eq_false]
  split_ifs <;> first | rfl | omega | exact congrArg (g _) (Fin.ext (by simp)) | (simp; intro; omega)
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
