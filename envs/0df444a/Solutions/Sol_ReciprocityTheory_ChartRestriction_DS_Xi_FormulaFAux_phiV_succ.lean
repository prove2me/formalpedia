-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.phiV_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:56.840217+00:00
-- url     : https://prove2.me/submissions/bec2245e-9099-482c-b5cb-16ebd9a6231f

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
theorem _root_.solution (k r' t : ℕ) (ht : t < r' + 1) (h : t + 1 < 1 + r' + 1) :
    phiV k (1 + r') ⟨t + 1, h⟩ = liftVec k 1 r' (phiV k r' ⟨t, ht⟩) := by
  funext p
  have hp := p.isLt
  simp only [phiV, liftVec, epsV_apply_eq, bvec_apply_eq_ite_val, esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]
  split_ifs <;> (try simp only [epsV_apply_eq, bvec_apply_eq_ite_val, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]) <;> (try split_ifs) <;>
    first | rfl | (exfalso; omega) | (simp_all; done) | omega
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
