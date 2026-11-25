-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.gaugeRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:58:56.04916+00:00
-- url     : https://prove2.me/submissions/a229f569-d3ed-4463-a61e-c9e6385daff8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_pair_index
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_coeff_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_cc_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_scale_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_prod_two_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_prod_pair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_eq_zero_of_pow_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_constantCoeff_logS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log


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
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution : GaugeRatioSt := by
  unfold GaugeRatioSt
  intro O _ _ k _ _ T _ rk χ cc hcc hunit r hr hfe
  obtain ⟨q, hq0, hrq⟩ : ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      r = PowerSeries.subst q (PowerSeries.exp k) :=
    ⟨_, WickVanishing.constantCoeff_logS hr, (WickVanishing.exp_log hr).symm⟩
  have hA : ∀ b : O, constantCoeff (scaleBy χ b q) = 0 := fun b => cc_scale χ b hq0
  have hE : ∀ b : O, scaleBy χ b r = PowerSeries.subst (scaleBy χ b q) (PowerSeries.exp k) := by
    intro b
    rw [hrq]
    exact scale_exp χ b hq0
  have key : ∀ a : O, scaleBy χ (1 + a * star a) q =
      scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q := by
    intro a
    have h1 := hfe a
    rw [hE, hE, hE] at h1
    rw [hrq] at h1
    have s1 : constantCoeff (scaleBy χ a q + scaleBy χ a q) = 0 := by rw [map_add, hA, add_zero]
    have s2 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q) = 0 := by rw [map_add, s1, hq0, add_zero]
    have s3 : constantCoeff (scaleBy χ a q + scaleBy χ a q + q + scaleBy χ (a * star a) q) = 0 := by
      rw [map_add, s2, hA, add_zero]
    apply WickVanishing.exp_inj (hA _) s3
    rw [h1, WickVanishing.exp_add s2 (hA _), WickVanishing.exp_add s1 hq0, WickVanishing.exp_add (hA _) (hA _)]
    ring
  have hcoef : ∀ (a : O) (m : GLet T rk →₀ ℕ),
      (m.prod fun l e => χ l.1 (1 + a * star a) ^ e) * coeff m q =
        ((m.prod fun l e => χ l.1 a ^ e) + (m.prod fun l e => χ l.1 a ^ e) + 1 +
          (m.prod fun l e => χ l.1 (a * star a) ^ e)) * coeff m q := by
    intro a m
    have h := congrArg (fun f => coeff m f) (key a)
    rw [map_add, map_add, map_add] at h
    simp only [coeff_scale] at h
    rw [h]
    ring
  refine ⟨q, hq0, ?_, ?_, hrq⟩
  · intro m hm
    by_contra hdeg
    have h := hcoef 1 m
    have t2 : ∀ l : GLet T rk, χ l.1 (1 + 1) = 2 := fun l => by
      rw [map_add, map_one, one_add_one_eq_two]
    have t1 : ∀ l : GLet T rk, χ l.1 1 = 1 := fun l => map_one _
    simp only [star_one, mul_one, t1, one_pow] at h
    simp only [t2] at h
    rw [prod_two_pow (k := k) m] at h
    have p1 : (m.prod fun (_ : GLet T rk) (_ : ℕ) => (1 : k)) = 1 := by simp [Finsupp.prod]
    rw [p1] at h
    exact hm (eq_zero_of_pow_sub hdeg (by linear_combination h))
  · intro l l' hne
    refine pair_index χ cc hcc hunit hne l.1 l'.1 (fun a => ?_)
    have h := hcoef a (Finsupp.single l 1 + Finsupp.single l' 1)
    rw [prod_pair, prod_pair, prod_pair] at h
    simp only [map_add, map_one, map_mul] at h
    linear_combination h
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
