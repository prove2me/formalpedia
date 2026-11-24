-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.hc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:14:19.973848+00:00
-- url     : https://prove2.me/submissions/53e0903a-c3b7-4d91-933e-0e9e25ce7670

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
private theorem bvec_dotProduct {n : ℕ} (v : Fin n → ℂ) (p : Fin n) : bvec p ⬝ᵥ v = v p := by
  simp [bvec, dotProduct, Pi.single_apply]
private theorem star_inv_sqrt_two' : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  first
    | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
    | simp [Complex.star_def]
    | simp
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
theorem _root_.solution (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (j : Fin (1 + r')) : (hcoord k r' x).1 j = AN k r' x.1 j.val := by
  have hj : j.val < r' + 1 := by omega
  show herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j)) = AN k r' x.1 j.val
  unfold AN herm
  rw [dif_pos hj]
  unfold phiV aF
  try simp only [Fin.coe_cast, Fin.val_mk]
  split_ifs with h
  · rw [star_bvec, bvec_dotProduct, Hpk_mulVec_apply_of_outer]
    · refine congrArg x.1 (Fin.ext ?_)
      simp only [esI, eI, Fin.val_mk]
      omega
    · simp only [esI, Fin.val_mk]
      omega
  · unfold epsV
    rw [star_smul, star_add, star_bvec, star_bvec, smul_dotProduct, add_dotProduct, bvec_dotProduct, bvec_dotProduct, star_inv_sqrt_two',
      Hpk_mulVec_apply_of_mem_middle, Hpk_mulVec_apply_of_val_eq_add]
    all_goals first
      | (simp only [smul_eq_mul, cc]; ring)
      | (simp [wI]; done)
      | (simp [wI]; omega)
      | omega
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
