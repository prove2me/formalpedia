-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.final_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:26.132431+00:00
-- url     : https://prove2.me/submissions/e412313b-42a1-4981-95db-bbcad8f443ec

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_sum_lt_split
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

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (N m : ℕ) (hm : m ≤ N) (A A' : ℕ → ℂ) (Uu b : ℂ) :
    let x : ℕ → ℂ := fun j => A' j - b * A j
    (1 + (∑ j ∈ Finset.range N, (star (A j) * A j + star (A' j) * A' j) + Uu + b * star b) -
        ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (A j) * A j) +
      (∑ j ∈ Finset.range m, star (x j) * A j) * (∑ j ∈ Finset.range m, star (A j) * x j) =
    (1 + ∑ j ∈ Finset.range m, star (A j) * A j) * ((1 + ∑ j ∈ Finset.range N, star (A j) * A j) + Uu +
        ∑ j ∈ Finset.range N, (if m ≤ j then star (A' j) * A' j else 0)) +
      (b + ∑ j ∈ Finset.range m, A' j * star (A j)) * star (b + ∑ j ∈ Finset.range m, A' j * star (A j)) := by
  intro x
  have hx1 : ∑ j ∈ Finset.range m, star (x j) * x j = ∑ j ∈ Finset.range m, star (A' j) * A' j -
      b * ∑ j ∈ Finset.range m, star (A' j) * A j - star b * ∑ j ∈ Finset.range m, star (A j) * A' j +
      b * star b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, star_sub, star_mul']
    ring
  have hx2 : ∑ j ∈ Finset.range m, star (x j) * A j = ∑ j ∈ Finset.range m, star (A' j) * A j -
      star b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x, star_sub, star_mul']
    ring
  have hx3 : ∑ j ∈ Finset.range m, star (A j) * x j = ∑ j ∈ Finset.range m, star (A j) * A' j -
      b * ∑ j ∈ Finset.range m, star (A j) * A j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x]
    ring
  have hq : ∑ j ∈ Finset.range m, A' j * star (A j) = ∑ j ∈ Finset.range m, star (A j) * A' j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hs : star (b + ∑ j ∈ Finset.range m, star (A j) * A' j) =
      star b + ∑ j ∈ Finset.range m, star (A' j) * A j := by
    rw [star_add, star_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [star_mul', star_star, mul_comm]
  rw [hx1, hx2, hx3, hq, hs, Finset.sum_add_distrib, sum_lt_split N m hm (fun j => star (A' j) * A' j)]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
