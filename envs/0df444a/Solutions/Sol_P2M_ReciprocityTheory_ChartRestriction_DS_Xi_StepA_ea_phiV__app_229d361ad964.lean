-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:40:57.004822+00:00
-- url     : https://prove2.me/submissions/df3adec3-4286-46f2-a084-dbe96abfc94c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos


section
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
private theorem mulVec_bvec_eq_fun_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  show ∑ l, M i l * bvec j l = M i j
  simp [bvec, Pi.single_apply]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r : ℕ} (hk : 1 ≤ k) (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV' k r b i = if b.val < r then (if i.val = b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) - (if i.val = r + k then 1 else 0)) := by
  simp only [phiV']
  by_cases h1 : b.val < r
  · rw [if_pos h1]
    simp only [phiV]
    rw [dif_pos h1, mulVec_bvec_eq_fun_apply]
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h1]
    simp only [phiV]
    rw [dif_neg h1, epsV, Matrix.mulVec_smul, Matrix.mulVec_add, mulVec_bvec_eq_fun_apply, mulVec_bvec_eq_fun_apply]
    have c1 : Hpk k r i (wI k r 0) = if i.val = r then 1 else 0 := by
      simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Nat.add_zero]
      split_ifs <;> first | rfl | (exfalso; omega)
    have c2 : Hpk k r i (wI k r (Fin.last k)) = -(if i.val = r + k then 1 else 0) := by
      simp only [Hpk, wI, Fin.ext_iff, Fin.val_last]
      split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, c1, c2]
    ring
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
