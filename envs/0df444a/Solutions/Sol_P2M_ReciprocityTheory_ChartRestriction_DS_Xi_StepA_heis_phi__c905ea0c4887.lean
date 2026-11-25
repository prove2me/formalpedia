-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_heis_phi__c905ea0c4887
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:25.588525+00:00
-- url     : https://prove2.me/submissions/24c0f2f1-825c-4b6c-806e-cab2829f0f0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_herm_phi_first_eq_zero
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
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section lev
variable (k r' : ℕ)
private lemma mulVec_bvec_eq_col_fun {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    H *ᵥ bvec j = fun i => H i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
private lemma phiV'_one_add_zero_eq_first_basis_e0_vec : phiV' k (1 + r') 0 = e0 k r' := by
  funext i
  simp only [phiV', phiV]
  rw [dif_pos (by first | simp | (rw [Fin.val_zero]; omega))]
  rw [mulVec_bvec_eq_col_fun]
  simp only [e0, bvec, Pi.single_apply, Hpk, esI, eI, a0, Fin.val_mk, Fin.ext_iff, Fin.val_zero]
  (try split_ifs) <;> (first | rfl | omega)
end lev
section dl
variable (k r : ℕ)
end dl
section a1
variable (k r' : ℕ)
end a1
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (hHA : HeisAct) (x : HPar k r') (b : Fin (1 + r' + 1)) :
    heis0 k r' x *ᵥ phiV' k (1 + r') b = phiV' k (1 + r') b -
      herm (Hpk k (1 + r')) (phiV' k (1 + r') b) (liftVec k 1 r' x.1) • phiV' k (1 + r') 0 := by
  simp only [heis0]
  rw [hHA k r', herm_phi_first_eq_zero k r' b, phiV'_one_add_zero_eq_first_basis_e0_vec k r']
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
