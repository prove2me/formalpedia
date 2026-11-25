-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.herm_last_lift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:30.132401+00:00
-- url     : https://prove2.me/submissions/a743b004-1c67-48f8-8054-e108a31753f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
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
private lemma herm_bvec_left' {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (w : Fin m → ℂ) :
    herm H (bvec a) w = ∑ i, star (w i) * H i a := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
private lemma liftVec_apply_of_edge (u : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1))
    (hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k) : liftVec k 1 r' u i = 0 := by
  simp only [liftVec]
  split_ifs <;> first | rfl | omega
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
theorem _root_.solution (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (es0 k r') (liftVec k 1 r' v) = 0 := by
  simp only [es0]
  rw [herm_bvec_left']
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val = 0
  · rw [liftVec_apply_of_edge k r' v i (Or.inl hi), star_zero, zero_mul]
  · have h0 : Hpk k (1 + r') i (esI k (1 + r') (a0 r')) = 0 := by
      first | (simp only [Hpk, eI, esI, a0, Fin.val_mk, Fin.ext_iff]; (try split_ifs) <;> (first | rfl | omega)) | (simp [Hpk, eI, esI, a0])
    rw [h0, mul_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
