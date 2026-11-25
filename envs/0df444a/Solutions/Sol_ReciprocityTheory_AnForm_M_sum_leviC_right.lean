-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.sum_leviC_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:31.243336+00:00
-- url     : https://prove2.me/submissions/aa033a2b-257d-4d29-a220-3915b766c42b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Theorems.Thm_ReciprocityTheory_AnForm_M_leviC_add_right
import Theorems.Thm_ReciprocityTheory_AnForm_M_leviC_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a x : Fin D → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by
  let ℓ : (Fin D → ℂ) →+ ℂ :=
    { toFun := leviC H a
      map_zero' := by simp [leviC]
      map_add' := leviC_add_right H a }
  have hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin D → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single (star x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := map_sum ℓ (fun j => star (x j) • (Pi.single j 1 : Fin D → ℂ)) Finset.univ
  rw [← hx] at this
  change leviC H a (star x) = ∑ j, leviC H a (star (x j) • Pi.single j 1) at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviC_smul_right]
  simp [mul_comm]
end ReciprocityTheory.AnForm.M
