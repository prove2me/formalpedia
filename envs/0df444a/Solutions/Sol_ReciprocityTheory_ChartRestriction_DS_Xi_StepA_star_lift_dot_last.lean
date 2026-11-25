-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.star_lift_dot_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:55.15441+00:00
-- url     : https://prove2.me/submissions/6cca8058-ff6d-4cd7-af22-f5e5b3b0a1e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_sum_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_goodRowsProjector_apply_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_last_basis_apply
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
section
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
private theorem e0_mp_eq_zero (j : Fin (2 * r' + k + 1)) : e0 k r' (mp k r' j) = 0 := by
  rw [goodRowsProjector_apply_eq_sum, if_neg]
  simp only [mp]
  omega
private theorem es0_mp_eq_zero (j : Fin (2 * r' + k + 1)) : es0 k r' (mp k r' j) = 0 := by
  have hj := j.isLt
  rw [last_basis_apply, if_neg]
  simp only [mp]
  omega
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) : star (liftVec k 1 r' v) ⬝ᵥ es0 k r' = 0 := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_split k r']
  simp [e0_mp_eq_zero, es0_mp_eq_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
