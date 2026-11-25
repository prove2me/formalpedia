-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.index_embedding_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:59.276993+00:00
-- url     : https://prove2.me/submissions/b668ed06-bab9-471d-872a-8a9006b7f927

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IndexEmbeddingBijective
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
theorem _root_.solution (k r' : ℕ) (hk : 1 ≤ k) : Function.Bijective (ix2 k r') := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro (a | a | a) (b | b | b) h <;>
      (have := a.isLt; have := b.isLt; simp [ix2, Fin.ext_iff] at h ⊢ <;> omega)
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
