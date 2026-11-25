-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.bco_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:05.757688+00:00
-- url     : https://prove2.me/submissions/694abb5d-9402-4701-a99b-14aed7e6ef23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_fsum_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hc1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hc2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_Uu_real
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
private theorem Hpk_mulVec_apply_of_outer (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h : i.val < r ∨ r + k < i.val) : (Hpk k r *ᵥ y) i = y ⟨2 * r + k - i.val, by omega⟩ := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
  · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm
private theorem Hpk_mulVec_apply_of_mem_middle (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val < r + k) : (Hpk k r *ᵥ y) i = y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · have e : Hpk k r i i = 1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm
private theorem Hpk_mulVec_apply_of_val_eq_add (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (h : i.val = r + k) : (Hpk k r *ᵥ y) i = -y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · have e : Hpk k r i i = -1 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, neg_one_mul]
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
    have hb2 := b.isLt
    have e : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, and_true, true_and] <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | omega | simp
    rw [e, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm
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
theorem _root_.solution (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    bco (hcoord k r' x) l = hb k r' x.1 x.2 + ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j) := by
  have hl := l.isLt
  have hB : ∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) =
      ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) := by
    rw [← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc1 k r' hk x j, hc2 k r' x j]
  have hC : ∑ j : Fin (1 + r'), (if l.val ≤ j.val then (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j) else 0) =
      ∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j) -
        ∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j) := by
    rw [← fsum_lt r' l.val (by omega) (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)),
      ← fsum r' (fun j => AN' k r' x.1 j * star (AN k r' x.1 j)), eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc1 k r' hk x j, hc2 k r' x j]
    split_ifs <;> first | (exfalso; omega) | simp
  have hD : herm (Hpk k r') x.1 x.1 = (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) +
      star (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) + Uu k r' x.1 := by
    set y := x.1 with hy
    have key2 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val →
        star (y a) * y b = y d * star (y c) := by
      intro a b c d h1 h2
      rw [Fin.ext h1, Fin.ext h2, mul_comm]
    have key3 : ∀ a b c d : Fin (2 * r' + k + 1), a.val = c.val → b.val = d.val →
        star (y a) * y b = star (y c) * y d := by
      intro a b c d h1 h2
      rw [Fin.ext h1, Fin.ext h2]
    set f : ℕ → ℂ := fun n => if h : n < 2 * r' + k + 1 then star (y ⟨n, h⟩) * (Hpk k r' *ᵥ y) ⟨n, h⟩ else 0
      with hf
    have hL : herm (Hpk k r') y y = ∑ n ∈ Finset.range (2 * r' + k + 1), f n := by
      rw [← Fin.sum_univ_eq_sum_range f (2 * r' + k + 1)]
      simp only [herm, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf, Pi.star_apply]
      rw [dif_pos i.isLt]
    have h1 : ∑ x ∈ Finset.range r', f x = ∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hf, AN, AN', aF, aF', Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_outer k r' y ⟨j, by omega⟩ (Or.inl (by simp only [Fin.val_mk]; omega))]
      exact key2 _ _ _ _ (by simp only [eI, Fin.val_mk]) (by simp only [esI, Fin.val_mk] <;> omega)
    have h2 : ∑ x ∈ Finset.range r', f (r' + 1 + (k - 1) + 1 + x) =
        star (∑ j ∈ Finset.range r', AN' k r' y j * star (AN k r' y j)) := by
      rw [star_sum, ← Finset.sum_range_reflect (fun j => star (AN' k r' y j * star (AN k r' y j))) r']
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hf, AN, AN', aF, aF', Fin.val_mk, star_mul', star_star]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_outer k r' y ⟨r' + 1 + (k - 1) + 1 + j, by omega⟩ (Or.inr (by simp only [Fin.val_mk]; omega))]
      exact key3 _ _ _ _ (by simp only [esI, Fin.val_mk] <;> omega) (by simp only [eI, Fin.val_mk] <;> omega)
    have h3 : ∑ x ∈ Finset.range (k - 1), f (r' + 1 + x) = Uu k r' y := by
      rw [← Fin.sum_univ_eq_sum_range (fun x => f (r' + 1 + x)) (k - 1)]
      unfold Uu
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.isLt
      simp only [hf]
      rw [dif_pos (by omega : r' + 1 + i.val < 2 * r' + k + 1),
        Hpk_mulVec_apply_of_mem_middle k r' y ⟨r' + 1 + i.val, by omega⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
      exact key3 _ _ _ _ (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
        (by first | (simp only [ix, Fin.val_mk]; omega) | (simp [ix]; omega) | simp [ix])
    have h4 : f r' + f (r' + 1 + (k - 1)) =
        AN' k r' y r' * star (AN k r' y r') + star (AN' k r' y r' * star (AN k r' y r')) := by
      simp only [hf, AN, AN', aF, aF', Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | skip
      rw [Hpk_mulVec_apply_of_mem_middle k r' y ⟨r', by omega⟩, Hpk_mulVec_apply_of_val_eq_add k r' y ⟨r' + 1 + (k - 1), by omega⟩]
      · rw [show (⟨r', by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' 0 from Fin.ext (by simp [wI]),
          show (⟨r' + 1 + (k - 1), by omega⟩ : Fin (2 * r' + k + 1)) = wI k r' (Fin.last k) from
            Fin.ext (by simp [wI]; omega)]
        simp only [cc, star_mul', star_sub, star_add, star_star, star_inv_sqrt_two']
        linear_combination (-(star (y (wI k r' 0)) * y (wI k r' 0) -
          star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * inv_sqrt_two_mul_inv_sqrt_two_mul_two_eq_one
      all_goals first | omega | (simp only [Fin.val_mk]; omega) | simp
    rw [hL, show Finset.range (2 * r' + k + 1) = Finset.range (r' + 1 + (k - 1) + 1 + r') by congr 1; omega,
      Finset.sum_range_add f (r' + 1 + (k - 1) + 1) r', Finset.sum_range_succ f (r' + 1 + (k - 1)),
      Finset.sum_range_add f (r' + 1) (k - 1), Finset.sum_range_succ f r',
      Finset.sum_range_succ (fun j => AN' k r' y j * star (AN k r' y j)) r', star_add, h1, h2, h3]
    linear_combination h4
  unfold bco
  rw [hC]
  have hT : (hcoord k r' x).2.2.2 = x.2 + (∑ j, (hcoord k r' x).2.1 j * star ((hcoord k r' x).1 j)).im := rfl
  rw [hT, hB]
  unfold hb
  rw [hD, ← Uu_real k r' x]
  generalize (∑ j ∈ Finset.range (r' + 1), AN' k r' x.1 j * star (AN k r' x.1 j)) = S
  generalize (∑ j ∈ Finset.range l.val, AN' k r' x.1 j * star (AN k r' x.1 j)) = R
  generalize (∑ i, ‖(hcoord k r' x).2.2.1 i‖ ^ 2) = U
  apply Complex.ext <;> simp [Complex.star_def] <;> ring
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
