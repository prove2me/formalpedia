-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:54.485505+00:00
-- url     : https://prove2.me/submissions/c3f85001-5ab0-41e3-8d58-dbcfd8133ddd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_e_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_e_es
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_e_l
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_es_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_es_es
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_es_l
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_l_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_d_l_es
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_e_e
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_e_es
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_e_l
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_es_e
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_es_es
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_es_l
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_l_e
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.d_l_es


section
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace FormulaFAux
private theorem star_bvec {n : ℕ} (p : Fin n) : star (bvec p) = bvec p := by
  funext q
  simp only [bvec, Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp
private theorem dotProduct_bvec {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : v ⬝ᵥ bvec p = v p := by
  simp [bvec, dotProduct, Pi.single_apply]
private theorem bvec_dotProduct {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : bvec p ⬝ᵥ v = v p := by
  simp [bvec, dotProduct, Pi.single_apply]
private theorem star_inv_sqrt_two' : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  first
    | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
    | simp [Complex.star_def]
    | simp
private theorem inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    norm_num at h2
  rw [← h2]
  field_simp
private theorem bvec_apply_eq_ite_val {n : ℕ} (p q : Fin n) : bvec p q = if q.val = p.val then 1 else 0 := by
  first
    | simp [bvec, Pi.single_apply, Fin.ext_iff]
    | (unfold bvec; rw [Pi.single_apply]; simp only [Fin.ext_iff])
    | (by_cases h : q = p
       · subst h; simp [bvec]
       · rw [if_neg (fun e => h (Fin.ext e))]; simp [bvec, h])
private theorem epsV_apply_eq (k r : ℕ) (q : Fin (2 * r + k + 1)) :
    epsV k r q = (Real.sqrt 2 : ℂ)⁻¹ * (bvec (wI k r 0) q + bvec (wI k r (Fin.last k)) q) := rfl
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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (i j : Fin (r + 1)) :
    star (phiV k r i) ⬝ᵥ phiV k r j = if i = j then 1 else 0 := by
  unfold phiV
  by_cases hi : i.val < r <;> by_cases hj : j.val < r
  · rw [dif_pos hi, dif_pos hj, star_bvec, dotProduct_bvec]
    simp only [bvec_apply_eq_ite_val, esI, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [dif_pos hi, dif_neg hj, star_bvec, bvec_dotProduct, if_neg (fun (e : i = j) => hj (e ▸ hi))]
    simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [dif_neg hi, dif_pos hj, dotProduct_bvec, if_neg (fun (e : i = j) => hi (e ▸ hj))]
    simp only [Pi.star_apply, epsV_apply_eq, bvec_apply_eq_ite_val, wI, esI, Fin.val_mk, Fin.val_zero, Fin.val_last]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [dif_neg hi, dif_neg hj, if_pos (Fin.ext (by omega))]
    have hv : (wI k r 0).val ≠ (wI k r (Fin.last k)).val := by
      simp only [wI, Fin.val_mk, Fin.val_zero, Fin.val_last]
      omega
    unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, star_inv_sqrt_two', smul_dotProduct, dotProduct_smul, add_dotProduct,
      dotProduct_add, dotProduct_add]
    simp only [dotProduct_bvec, smul_eq_mul]
    simp only [bvec_apply_eq_ite_val, if_neg hv, if_neg (Ne.symm hv), eq_self_iff_true, if_true]
    linear_combination inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
