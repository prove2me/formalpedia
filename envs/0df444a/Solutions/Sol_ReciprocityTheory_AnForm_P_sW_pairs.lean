-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.sW_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:41.961494+00:00
-- url     : https://prove2.me/submissions/00a9ffea-7ef5-403b-8ccc-421d98bb1c69

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m w = ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
      hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0 := by
  let F : Fin N × Fin N → ℝ := fun q =>
    if q.1.val < m ∧ m ≤ q.2.val then hd q.2 / hd q.1 * ‖zMat N w q.2 q.1‖ ^ 2 else 0
  calc sW N hd m w = ∑ q, F q := (Fintype.sum_prod_type' (fun i k => F (i, k))).symm
    _ = ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2), F q := by
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hlt
      apply hq
      simp only [F]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hlt (Fin.lt_iff_val_lt_val.2 (by omega))
    _ = ∑ p : Pairs N, F p.1 := Finset.sum_subtype _ (by simp) F
    _ = _ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [F, zMat_apply, dif_pos p.2]
end ReciprocityTheory.AnForm.P
