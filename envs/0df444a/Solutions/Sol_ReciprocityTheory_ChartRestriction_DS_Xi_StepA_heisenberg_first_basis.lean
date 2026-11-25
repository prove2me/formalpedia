-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.heisenberg_first_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:15.575825+00:00
-- url     : https://prove2.me/submissions/1c0a76ba-c745-42b0-a232-21b9a715177b

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
private theorem dotProduct_bvec_eq_apply {m : ℕ} (w : Fin m → ℂ) (j : Fin m) : w ⬝ᵥ bvec j = w j := by
  show ∑ i, w i * bvec j i = w j
  simp [bvec, Pi.single_apply]
private theorem e0_apply_eq_ite (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    e0 k r' p = if p.val = 0 then 1 else 0 := by
  simp only [e0, bvec, Pi.single_apply, eI, a0, Fin.ext_iff]
private theorem es0_apply_eq_ite (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' p = if p.val = 2 * (1 + r') + k then 1 else 0 := by
  simp only [es0, bvec, Pi.single_apply, esI, a0, Fin.ext_iff, Nat.sub_zero]
private theorem liftVec_apply_eq_zero_of_edge (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : liftVec k 1 r' v q = 0 := by
  simp only [liftVec]
  split_ifs with h
  · exfalso; omega
  · rfl
private theorem Hpk_mulVec_e0_eq_es0_vec (k r' : ℕ) : Hpk k (1 + r') *ᵥ e0 k r' = es0 k r' := by
  funext p
  have hp := p.isLt
  show ∑ q, Hpk k (1 + r') p q * e0 k r' q = es0 k r' p
  rw [es0_apply_eq_ite, Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · rw [e0_apply_eq_ite]
    simp only [and_true, true_and, Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)
  · intro q _ hq
    have hq' : q.val ≠ 0 := fun h => hq (Fin.ext h)
    rw [e0_apply_eq_ite, if_neg hq', mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
private theorem herm_e0_left_eq_star_apply_last (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (e0 k r') w = star (w ⟨2 * (1 + r') + k, by omega⟩) := by
  rw [herm, Hpk_mulVec_e0_eq_es0_vec, es0, dotProduct_bvec_eq_apply]
  rfl
private theorem e0_apply_last_eq_zero (k r' : ℕ) : e0 k r' ⟨2 * (1 + r') + k, by omega⟩ = 0 := by
  rw [e0_apply_eq_ite]
  exact if_neg (show ¬(2 * (1 + r') + k = 0) by omega)
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
theorem _root_.solution {k r' : ℕ} (hHA : HeisAct) (x : HPar k r') : heis0 k r' x *ᵥ e0 k r' = e0 k r' := by
  rw [heis0, hHA k r', herm_e0_left_eq_star_apply_last, herm_e0_left_eq_star_apply_last,
    liftVec_apply_eq_zero_of_edge k r' x.1 ⟨2 * (1 + r') + k, by omega⟩ (Or.inr rfl), e0_apply_last_eq_zero]
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
