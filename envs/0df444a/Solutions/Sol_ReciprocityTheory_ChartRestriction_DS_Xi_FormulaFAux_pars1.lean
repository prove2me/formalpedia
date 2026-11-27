-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.pars1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:00.553319+00:00
-- url     : https://prove2.me/submissions/c1434e71-cb87-4d4a-b134-a926de5d9c3d

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
    star y ⬝ᵥ y = ∑ t : Fin (r' + 1), (star (aF k r' y t) * aF k r' y t + star (aF' k r' y t) * aF' k r' y t) +
      ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i))) := by
  have hcc := star_cc_mul_cc
  have hb := ix_bij k r' hk
  rw [dotProduct, ← (Equiv.ofBijective _ hb).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have htl := t.isLt
  simp only [Equiv.ofBijective_apply, Pi.star_apply]
  unfold aF aF'
  by_cases ht : (t : ℕ) < r'
  · rw [dif_pos ht, dif_pos ht]
    rfl
  · rw [dif_neg ht, dif_neg ht]
    have h0 : ix k r' (Sum.inl t) = wI k r' 0 := rankOne_base_weight_eq_cmTheta k r' t ht _
    have h1 : ix k r' (Sum.inr (Sum.inl t)) = wI k r' (Fin.last k) := wk_eq k r' t ht _
    rw [h0, h1]
    simp only [star_mul', star_sub, star_add]
    linear_combination (-(2 * star (y (wI k r' 0)) * y (wI k r' 0) +
      2 * star (y (wI k r' (Fin.last k))) * y (wI k r' (Fin.last k)))) * hcc
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
