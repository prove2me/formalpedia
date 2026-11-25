-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.herm_lift_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:34.62052+00:00
-- url     : https://prove2.me/submissions/16c99d1b-23b2-482a-a410-c955b41c748f

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
private lemma liftVec_apply_of_edge (u : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1))
    (hi : i.val = 0 ∨ i.val = 2 * (1 + r') + k) : liftVec k 1 r' u i = 0 := by
  simp only [liftVec]
  split_ifs <;> first | rfl | omega
private lemma liftVec_apply_succ (u : Fin (2 * r' + k + 1) → ℂ) (a : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' u ⟨a.val + 1, by omega⟩ = u a := by
  simp only [liftVec, Fin.val_mk]
  rw [dif_pos (by omega)]
  exact congrArg u (Fin.ext (by show a.val + 1 - 1 = a.val; omega))
private lemma Hpk_one_add_apply_succ_succ (a b : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ = Hpk k r' a b := by
  simp only [Hpk, Fin.val_mk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega
private lemma sum_eq_sum_succ_of_zero_at_edges (f : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hf : ∀ i : Fin (2 * (1 + r') + k + 1), (i.val = 0 ∨ i.val = 2 * (1 + r') + k) → f i = 0) :
    ∑ i, f i = ∑ a : Fin (2 * r' + k + 1), f ⟨a.val + 1, by omega⟩ := by
  have hinj : Function.Injective
      (fun a : Fin (2 * r' + k + 1) => (⟨a.val + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  symm
  apply Fintype.sum_of_injective _ hinj
  · intro i hi
    apply hf
    by_contra hne
    apply hi
    exact ⟨⟨i.val - 1, by omega⟩, Fin.ext (by show i.val - 1 + 1 = i.val; omega)⟩
  · intro a
    rfl
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
theorem _root_.solution (u v : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' u) (liftVec k 1 r' v) = herm (Hpk k r') u v := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec]
  rw [sum_eq_sum_succ_of_zero_at_edges]
  · apply Finset.sum_congr rfl
    intro a _
    rw [sum_eq_sum_succ_of_zero_at_edges]
    · simp only [Pi.star_apply, liftVec_apply_succ, Hpk_one_add_apply_succ_succ]
    · intro j hj
      rw [liftVec_apply_of_edge k r' u j hj, mul_zero]
  · intro i hi
    rw [Pi.star_apply, liftVec_apply_of_edge k r' v i hi, star_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
