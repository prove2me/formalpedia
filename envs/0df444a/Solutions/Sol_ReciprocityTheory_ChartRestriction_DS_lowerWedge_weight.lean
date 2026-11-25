-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowerWedge_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:09.177299+00:00
-- url     : https://prove2.me/submissions/dfc3669a-8d95-40ad-b665-59a5802e2fbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cfa_rho_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockBasis_wt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n (lowerWedgeAlt ε).1) =
      (((rhoHol ε - rhoN ε) c : ℝ) : ℂ) • fockBasis n (lowerWedgeAlt ε).1 := by
  have hw : fockWt ε (lowerWedgeAlt ε).1 c = (rhoHol ε - rhoN ε) c := by
    rw [cfa_rho_coord, fockWt, Finset.sum_apply]
    have hS : (lowerWedgeAlt ε).1 = univ.filter fun k => ε (finProdFinEquiv.symm k).1 = true ∧
        ε (finProdFinEquiv.symm k).2 = false ∧ (finProdFinEquiv.symm k).2 < (finProdFinEquiv.symm k).1 := by
      ext k
      simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hS, Finset.sum_filter, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    have key : ∀ i b : Fin n, (if ε i = true ∧ ε b = false ∧ b < i then modeWt ε (i, b) c else 0) =
        (if c = i then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) -
        (if c = b then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) := by
      intro i b
      by_cases h : ε i = true ∧ ε b = false ∧ b < i
      · simp only [if_pos h]
        simp only [modeWt, if_pos (And.intro h.1 h.2.1), root, Pi.sub_apply, Pi.single_apply]
      · simp only [if_neg h]
        simp
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => key i b]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp
    · simp
  rw [fockBasis_wt, hw]
end ReciprocityTheory.ChartRestriction.DS
