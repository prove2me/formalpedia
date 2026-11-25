-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:30.503548+00:00
-- url     : https://prove2.me/submissions/6dc9ba1c-7091-4a25-a292-3ccfdbf29870

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_coeff_expX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_single_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_coeff_sum_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable (A : Type) [CommRing A] [Algebra ℚ A]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) A) + X 1) (PowerSeries.exp A) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A) (PowerSeries.exp A) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A) (PowerSeries.exp A) := by
  ext e
  have ha : PowerSeries.HasSubst ((X 0 : MvPowerSeries (Fin 2) A) + X 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.coeff_subst ha, MvPowerSeries.coeff_mul]
  simp_rw [gt_coeff_sum_pow A, gt_coeff_expX A, PowerSeries.coeff_exp]
  rw [finsum_eq_single _ (e 0 + e 1)]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single (single 0 (e 0), single 1 (e 1))]
    · simp only [Finsupp.single_eq_same, eq_self_iff_true, if_true, ite_true]
      rw [smul_eq_mul, ← map_natCast (algebraMap ℚ A), ← map_mul, ← map_mul]
      congr 1
      have f0 : ((e 0 + e 1).factorial : ℚ) ≠ 0 := by positivity
      have f1 : ((e 0).factorial : ℚ) ≠ 0 := by positivity
      have f2 : ((e 1).factorial : ℚ) ≠ 0 := by positivity
      rw [Nat.cast_choose ℚ (Nat.le_add_right (e 0) (e 1)), Nat.add_sub_cancel_left]
      field_simp
      all_goals ring
    · intro p hp hne
      have hp' : p.1 + p.2 = e := by simpa using hp
      by_cases h1 : p.1 = single 0 (p.1 0)
      · by_cases h2 : p.2 = single 1 (p.2 1)
        · exfalso
          have a1 : p.2 0 = 0 := by
            rw [h2]
            simp
          have a2 : p.1 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hp' 0
          have c1 := DFunLike.congr_fun hp' 1
          simp only [Finsupp.add_apply] at c0 c1
          apply hne
          refine Prod.ext ?_ ?_
          · show p.1 = single 0 (e 0)
            rw [h1]
            congr 1
            omega
          · show p.2 = single 1 (e 1)
            rw [h2]
            congr 1
            omega
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro hnot
      exfalso
      apply hnot
      simpa using (gt_single_add e).symm
  · intro d hd
    rw [if_neg (fun h => hd h.symm), smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
