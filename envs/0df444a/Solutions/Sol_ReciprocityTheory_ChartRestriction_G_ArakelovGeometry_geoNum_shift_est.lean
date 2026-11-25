-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_shift_est
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:54.683542+00:00
-- url     : https://prove2.me/submissions/79e1d751-d3a0-4f12-b230-c387db09119d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_sub_prod_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_le_nrm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_nrm_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_geoNum_expand_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (x c : K → ℤ) :
    |(geoNum n V (fun _ => x) : ℝ) - geoNum n V (fun _ => x - c)| ≤
      coefB n V * (n * nrm c * (nrm x + 1 + nrm c) ^ (n - 1)) := by
  rw [geoNum_expand_real n V hS, geoNum_expand_real n V hS, ← Finset.sum_sub_distrib, coefB,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_sub_prod_le (Finset.univ : Finset (Fin n)) (fun i => (x (r i) : ℝ))
    (fun i => (c (r i) : ℝ)) (Y := nrm x + 1) (E := nrm c) (by linarith [nrm_nonneg x]) (nrm_nonneg c)
    (fun i _ => (abs_le_nrm x _).trans (by linarith)) (fun i _ => abs_le_nrm c _)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  simp only [Pi.sub_apply, Int.cast_sub]
  exact this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
