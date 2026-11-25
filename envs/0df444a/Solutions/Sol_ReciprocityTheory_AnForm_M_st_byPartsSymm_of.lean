-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_byPartsSymm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:13.155819+00:00
-- url     : https://prove2.me/submissions/7e70d2cc-eb8a-42e6-b5ad-fa1cf76d2b09

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_symm_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_exists_good_partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_isPotential_cons
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_cons_finset_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_finset_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_continuous
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : ReciprocityTheory.AnForm.A.PartsStatement) : ByPartsSymmStatement := by
  intro e X _ _ _ A v w hv hw Φ hΦ
  obtain ⟨M, θ, G, j, x0, hθs, -, hθ1, hθG, hGo, hGs, hGU⟩ := st_exists_good_partition A Φ
  have hsum : (fun x => ∑ m, θ m x * v x) = v := by
    funext x
    rw [← Finset.sum_mul, hθ1, one_mul]
  have hL := st_mInt_finset_sum A _ (st_isPotential_cons A hw hΦ) Finset.univ
    (fun m x => θ m x * v x) (fun m => st_smooth_continuous A (st_smooth_mul A (hθs m) hv))
  have hR := st_mInt_cons_finset_sum A Φ hΦ Finset.univ (fun m x => θ m x * v x)
    (fun m => st_smooth_mul A (hθs m) hv) w (st_smooth_continuous A hw)
  rw [hsum] at hL hR
  rw [hL, hR]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact st_symm_piece A Φ hΦ (j m) (G m) (hGo m) (hGs m) (x0 m) (hGU m) hP w _ hw
    (st_smooth_mul A (hθs m) hv) ((tsupport_mul_subset_left).trans (hθG m))
end ReciprocityTheory.AnForm.M
