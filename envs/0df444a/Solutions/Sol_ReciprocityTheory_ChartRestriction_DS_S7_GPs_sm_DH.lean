-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.sm_DH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:02.592955+00:00
-- url     : https://prove2.me/submissions/2743de64-1490-4c1b-8666-7747f9a5cfba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_mmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_isOpen_kappaOpenNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Wset n)) : ContDiffOn ℂ ∞ (DH X g) (Wset n) := by
  have h2 : ContDiff ℂ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      ((X * p.1, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
    (contDiff_mmul contDiff_const contDiff_fst).prodMk contDiff_const
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    first | simp | (exact_mod_cast le_rfl) | norm_cast | exact le_of_eq (by rfl)
  exact (hg.fderiv_of_isOpen isOpen_kappaOpenNeighbourhood hmn).clm_apply h2.contDiffOn
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
