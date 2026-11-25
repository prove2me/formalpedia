-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_pars1__8f9192c16c33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:28.571677+00:00
-- url     : https://prove2.me/submissions/fb6f5671-c93e-4187-82a9-113adaef1e36

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
    star y ⬝ᵥ y = ∑ j ∈ Finset.range (r' + 1), (star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) +
      Uu k r' y := by
  have key : ∀ a b : Fin (2 * r' + k + 1), a.val = b.val → star (y a) * y a = star (y b) * y b := by
    intro a b h
    rw [Fin.ext h]
  set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * y ⟨n, h⟩ else 0 with hf
  have hL : star y ⬝ᵥ y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n := by
    rw [← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf, Pi.star_apply]
    rw [dif_pos i.isLt]
  have h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', star (AN k r' y j) * AN k r' y j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hf, AN, aF, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [eI, Fin.val_mk])
  have h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) =
      ∑ j ∈ Finset.range r', star (AN' k r' y j) * AN' k r' y j := by
    rw [← Finset.sum_range_reflect (fun j => star (AN' k r' y j) * AN' k r' y j) r']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hf, AN', aF', Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | exact key _ _ (by simp only [esI, Fin.val_mk]; omega)
  have h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]
    unfold Uu
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    simp only [hf]
    rw [dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1)]
    exact key _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
  have h4 : f r' + f (r' + 1 + (k - 1)) =
      star (AN k r' y r') * AN k r' y r' + star (AN' k r' y r') * AN' k r' y r' := by
    simp only [hf, AN, AN', aF, aF', Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | skip
    rw [show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]),
      show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from
        Fin.ext (by simp [wI]; omega)]
    simp only [cc, star_mul', star_sub, star_add, star_inv_sqrt_two']
    linear_combination (-(star (y (wI k r' 0)) * y (wI k r' 0) +
      star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
  rw [hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega,
    Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)),
    Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r',
    Finset.sum_range_succ (fun j => star (AN k r' y j) * AN k r' y j + star (AN' k r' y j) * AN' k r' y j) r',
    Finset.sum_add_distrib, h1, h2, h3]
  linear_combination h4
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
