-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.pars2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:29:41.646089+00:00
-- url     : https://prove2.me/submissions/e689d196-5d3f-4810-8ea7-0fb3f72229d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_es_es
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_e_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_es_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_e_es
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_es_l
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_e_l
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_l_es
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_l_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hmv_mid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hmv_out
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_ix_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_rankOne_base_weight_eq_cmTheta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_wk_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_es_es
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_e_e
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_es_e
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_e_es
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_es_l
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_e_l
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_l_es
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_l_e
section
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace FormulaFAux
private theorem Hpk_mulVec_apply_eq_ite (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ y) v = if (v : ℕ) < r ∨ r + k < (v : ℕ) then y ⟨2 * r + k - v, by omega⟩
      else if (v : ℕ) = r + k then -y v else y v := by
  have hv := v.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h1 : (v : ℕ) < r ∨ r + k < (v : ℕ)
  · rw [if_pos h1, Finset.sum_eq_single ⟨2 * r + k - v, by omega⟩]
    · rcases h1 with h1 | h1
      · simp only [Hpk, Fin.val_mk]
        rw [if_pos ⟨h1, by omega⟩, one_mul]
      · simp only [Hpk, Fin.val_mk]
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 2 * r + k - v := fun e => hj (Fin.ext e)
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (fun hc => by have := hc.1; have := hc.2.1; omega),
        zero_mul]
    · simp
  · rw [if_neg h1, Finset.sum_eq_single v]
    · simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, by trivial⟩]
      by_cases h2 : (v : ℕ) = r + k
      · rw [if_pos h2, if_pos h2, neg_one_mul]
      · rw [if_neg h2, if_neg h2, one_mul]
    · intro j _ hj
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (fun hc => by have := hc.1; have := hc.2; omega),
        if_neg (fun hc => hj hc.2.2.symm), zero_mul]
    · simp
private theorem Hpk_mulVec_apply_wI_zero (k r' : ℕ) (hk : 1 ≤ k) (x : Fin (2 * r' + k + 1) → ℂ) :
    (Hpk k r' *ᵥ x) (wI k r' 0) = x (wI k r' 0) := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega),
    if_neg (by simp only [wI, Fin.val_zero, Fin.val_mk]; omega)]
private theorem Hpk_mulVec_apply_wI_last (k r' : ℕ) (x : Fin (2 * r' + k + 1) → ℂ) :
    (Hpk k r' *ᵥ x) (wI k r' (Fin.last k)) = -x (wI k r' (Fin.last k)) := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [wI, Fin.val_last, Fin.val_mk]; omega),
    if_pos (by simp only [wI, Fin.val_last, Fin.val_mk])]
private theorem star_cc_mul_cc : star cc * cc = (1 / 2 : ℂ) := by
  unfold cc
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
end FormulaFAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (k r' : ℕ) (hk : 1 ≤ k) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k r') y y = ∑ t : Fin (r' + 1), (star (aF k r' y t) * aF' k r' y t + star (aF' k r' y t) * aF k r' y t) +
      ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i))) := by
  have hcc := star_cc_mul_cc
  have hb := ix_bij k r' hk
  rw [herm, dotProduct, ← (Equiv.ofBijective _ hb).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have htl := t.isLt
  simp only [Equiv.ofBijective_apply, Pi.star_apply]
  unfold aF aF'
  by_cases ht : (t : ℕ) < r'
  · rw [dif_pos ht, dif_pos ht]
    have h1 : (Hpk k r' *ᵥ y) (ix k r' (Sum.inl t)) = y (ix k r' (Sum.inr (Sum.inl t))) :=
      hmv_out k r' y (t : ℕ) _ (Or.inl ht)
    have h2 : (Hpk k r' *ᵥ y) (ix k r' (Sum.inr (Sum.inl t))) = y (ix k r' (Sum.inl t)) := by
      rw [show ix k r' (Sum.inr (Sum.inl t)) = ⟨2 * r' + k - (t : ℕ), by omega⟩ from rfl,
        hmv_out k r' y _ _ (Or.inr (by omega))]
      congr 1
      ext
      show 2 * r' + k - (2 * r' + k - (t : ℕ)) = (t : ℕ)
      omega
    rw [h1, h2]
    rfl
  · rw [dif_neg ht, dif_neg ht]
    have h0 : ix k r' (Sum.inl t) = wI k r' 0 := rankOne_base_weight_eq_cmTheta k r' t ht _
    have h1 : ix k r' (Sum.inr (Sum.inl t)) = wI k r' (Fin.last k) := wk_eq k r' t ht _
    rw [h0, h1, Hpk_mulVec_apply_wI_zero k r' hk y, Hpk_mulVec_apply_wI_last k r' y]
    simp only [star_mul', star_sub, star_add]
    linear_combination (-(2 * star (y (wI k r' 0)) * y (wI k r' 0) -
      2 * star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * hcc
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [Equiv.ofBijective_apply, Pi.star_apply]
  congr 1
  exact hmv_mid k r' y (r' + (i : ℕ) + 1) (by omega) (by omega) (by omega)
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
