-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.rhoSq_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:02.746576+00:00
-- url     : https://prove2.me/submissions/9b060b80-0aea-43d3-a8f5-83b12ce73dff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_nsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hc2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_Uu_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_Lsq_c
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



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    (rhoSq (hcoord k r' x) l : ℂ) = (1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j) +
      Uu k r' x.1 + ∑ j ∈ Finset.range (r' + 1), (if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0) := by
  have hL : (Lsq (hcoord k r' x) (Fin.last (1 + r')) : ℂ) =
      1 + ∑ j ∈ Finset.range (r' + 1), star (AN k r' x.1 j) * AN k r' x.1 j := by
    rw [Lsq_c k r' hk x, Fin.val_last, Nat.add_comm 1 r']
  unfold rhoSq
  rw [Complex.ofReal_add, Complex.ofReal_add, hL, Uu_real, Complex.ofReal_sum]
  congr 1
  rw [← fsum r' (fun j => if l.val ≤ j then star (AN' k r' x.1 j) * AN' k r' x.1 j else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [nsq, hc2 k r' x j]
  · simp
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
