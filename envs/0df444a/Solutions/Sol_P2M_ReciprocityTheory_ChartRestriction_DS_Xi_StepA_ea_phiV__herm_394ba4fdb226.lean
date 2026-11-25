-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__herm_394ba4fdb226
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:25.2688+00:00
-- url     : https://prove2.me/submissions/0b8cd351-bcc8-4c9f-ba90-4b1c1c0514ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV_app
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__app_229d361ad964
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_sum_ind
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
private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [and_true, true_and, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | (simp; done) | norm_num
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun h => hl (Fin.ext h)
      have : Hpk k r i l = 0 := by
        simp only [and_true, true_and, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [and_true, true_and, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | (simp; done) | norm_num
    · intro l _ hl
      have hl' : l.val ≠ 2 * r + k - i.val := fun h => hl (Fin.ext h)
      have : Hpk k r i l = 0 := by
        simp only [and_true, true_and, Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
private theorem star_inv_sqrt_two_mul_sum_ite_eq_sub (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + k + 1)) :
    star (((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) - (if i.val = r + k then 1 else 0))) *
      (((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0))) =
    star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * (if i.val = r then 1 else 0) -
      star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * (if i.val = r + k then 1 else 0) := by
  split_ifs <;> first | (exfalso; omega) | (simp; done) | (simp; ring) | ring
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
theorem _root_.solution {k r : ℕ} (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  have e : Hpk k r *ᵥ phiV' k r a = phiV k r a := by
    rw [phiV', Matrix.mulVec_mulVec, hpk_sq_lemma, Matrix.one_mulVec]
  rw [herm, e]
  show ∑ i, star (phiV' k r b i) * phiV k r a i = 0
  simp only [ea_phiV'_app hk, ea_phiV_app]
  have ha := a.isLt
  have hb := b.isLt
  by_cases h1 : a.val < r <;> by_cases h2 : b.val < r
  · simp only [if_pos h1, if_pos h2]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> first | (exfalso; omega) | simp
  · simp only [if_pos h1, if_neg h2]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> first | (exfalso; omega) | simp
  · simp only [if_neg h1, if_pos h2]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> first | (exfalso; omega) | simp
  · simp only [if_neg h1, if_neg h2, star_inv_sqrt_two_mul_sum_ite_eq_sub k r hk]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ea_sum_ind (n := 2 * r + k + 1) r (by omega), ea_sum_ind (n := 2 * r + k + 1) (r + k) (by omega), sub_self]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
