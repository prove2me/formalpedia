-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.hmv_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:33.824002+00:00
-- url     : https://prove2.me/submissions/e6fe1ba3-f1d8-44d7-aaf1-a32710a66e78

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
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (h : r + k < 2 * r + k + 1) :
    (Hpk k r *ᵥ y) ⟨r + k, h⟩ = -y ⟨r + k, h⟩ := by
  rw [Hpk_mulVec_apply_eq_ite, if_neg (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk])]
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
