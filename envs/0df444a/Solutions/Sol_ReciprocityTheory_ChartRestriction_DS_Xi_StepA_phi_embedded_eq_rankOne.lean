-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.phi_embedded_eq_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:12.652214+00:00
-- url     : https://prove2.me/submissions/ef193b51-b4fc-451f-877e-fef41917dbff

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
private theorem w0_mul_apply_zero (k r' : ℕ) (c : ℂ) (M : Mat k (1 + r')) (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0) : (w0 k r' c * M) p q = (star c)⁻¹ * M ⟨2 * (1 + r') + k, by omega⟩ q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨2 * (1 + r') + k, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · congr 1
    simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro l _ hl
    have hl' : l.val ≠ 2 * (1 + r') + k := fun h => hl (Fin.ext h)
    have : w0 k r' c p l = 0 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
private theorem w0_mul_apply_last (k r' : ℕ) (c : ℂ) (M : Mat k (1 + r')) (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 2 * (1 + r') + k) : (w0 k r' c * M) p q = c * M ⟨0, by omega⟩ q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * (1 + r') + k + 1))]
  · congr 1
    simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro l _ hl
    have hl' : l.val ≠ 0 := fun h => hl (Fin.ext h)
    have : w0 k r' c p l = 0 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
private theorem w0_mul_apply_of_middle (k r' : ℕ) (c : ℂ) (M : Mat k (1 + r')) (p q : Fin (2 * (1 + r') + k + 1))
    (hp0 : 0 < p.val) (hpN : p.val < 2 * (1 + r') + k) : (w0 k r' c * M) p q = M p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · have : w0 k r' c p p = 1 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, one_mul]
  · intro l _ hl
    have hl' : l.val ≠ p.val := fun h => hl (Fin.ext h)
    have : w0 k r' c p l = 0 := by
      simp only [w0, Fin.ext_iff, and_true, true_and, eq_self_iff_true]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
private theorem Hpk_one_add_apply_mp_mp (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (mp k r' i) (mp k r' j) = Hpk k r' i j := by
  have hi := i.isLt
  have hj := j.isLt
  have e1 : (mp k r' i).val = i.val + 1 := rfl
  have e2 : (mp k r' j).val = j.val + 1 := rfl
  simp only [and_true, true_and, Hpk, Fin.ext_iff, e1, e2]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all
private theorem lev_apply_eq_ite_of_outer (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]
private theorem lev_apply_mp_mp (k r' : ℕ) (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (mp k r' i) (mp k r' j) = g i j := by
  have hi := i.isLt
  have hj := j.isLt
  have h1 : 1 ≤ (mp k r' i).val ∧ (mp k r' i).val < 2 * r' + k + 1 + 1 := by simp only [mp]; omega
  have h2 : 1 ≤ (mp k r' j).val ∧ (mp k r' j).val < 2 * r' + k + 1 + 1 := by simp only [mp]; omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  all_goals (congr 1 <;> first | exact Fin.ext (Nat.add_sub_cancel _ 1) | (apply Fin.ext; simp [mp]))
private theorem w0_one_mul_Hpk_eq_lev_Hpk (k r' : ℕ) : w0 k r' 1 * Hpk k (1 + r') = ιLev k 1 r' (Hpk k r') := by
  ext p q
  have hp := p.isLt
  have hq := q.isLt
  by_cases hp0 : p.val = 0
  · rw [w0_mul_apply_zero k r' 1 _ p q hp0, lev_apply_eq_ite_of_outer k r' _ p q (by omega)]
    simp only [and_true, true_and, Hpk, Fin.ext_iff, star_one, inv_one, one_mul]
    split_ifs <;> first | rfl | (exfalso; omega)
  · by_cases hpN : p.val = 2 * (1 + r') + k
    · rw [w0_mul_apply_last k r' 1 _ p q hpN, lev_apply_eq_ite_of_outer k r' _ p q (by omega)]
      simp only [and_true, true_and, Hpk, Fin.ext_iff, one_mul]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [w0_mul_apply_of_middle k r' 1 _ p q (by omega) (by omega)]
      by_cases hqm : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
      · obtain ⟨p', rfl⟩ : ∃ p' : Fin (2 * r' + k + 1), p = mp k r' p' :=
          ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp only [mp]; omega)⟩
        obtain ⟨q', rfl⟩ : ∃ q' : Fin (2 * r' + k + 1), q = mp k r' q' :=
          ⟨⟨q.val - 1, by omega⟩, Fin.ext (by simp only [mp]; omega)⟩
        rw [lev_apply_mp_mp, Hpk_one_add_apply_mp_mp]
      · simp only [ιLev, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
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
theorem _root_.solution (k r' : ℕ) (a : Fin (1 + r' + 1)) : phi2 k r' a = w0 k r' 1 *ᵥ phiV' k (1 + r') a := by
  rw [phi2, phiV', Matrix.mulVec_mulVec, w0_one_mul_Hpk_eq_lev_Hpk]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
