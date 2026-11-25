-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holoWeak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:34.185571+00:00
-- url     : https://prove2.me/submissions/8ffb7693-89ac-44b3-90a2-2296eed22316

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_Lemmata_MiscLemmasF_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoWeak_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : HoloWeakStatement := by
  intro n Ω u hΩ hu
  refine ⟨hu.continuousOn.locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro g hg v
  obtain ⟨hgs, hgc, hgΩ⟩ := hg
  have hK : IsCompact (tsupport g) := hgc
  have huK : ContinuousOn u (tsupport g) := hu.continuousOn.mono hgΩ
  have hg1 : ContDiff ℝ 1 g := hgs.of_le (by exact_mod_cast le_top)
  have hgd : Differentiable ℝ g := hg1.differentiable one_ne_zero
  have hg'c : ∀ w : V n, Continuous fun x => fderiv ℝ g x w := fun w =>
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hzero : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hzero' : ∀ w x, x ∉ tsupport g → fderiv ℝ g x w = 0 := fun w x hx => by
    rw [fderiv_of_notMem_tsupport ℝ hx]; rfl
  have hint : ∀ h : V n → ℂ, Continuous h → (∀ x, x ∉ tsupport g → h x = 0) →
      Integrable (fun x => u x * h x) := by
    intro h hh hh0
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport g) ?_ ?_
    · exact (huK.mul hh.continuousOn).integrableOn_compact hK
    · intro x hx; simp [hh0 x hx]
  have hgi : Integrable g := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hibp : ∀ w : V n, ∫ x, u x * fderiv ℝ g x w = - ∫ x, fderiv ℝ u x w * g x := by
    intro w
    obtain ⟨C, hC⟩ := holoWeak_bound hΩ hu hK hgΩ w
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · refine Integrable.mono' (hgi.norm.const_mul C) ?_ (Eventually.of_forall fun x => ?_)
      · exact (measurable_fderiv_apply_const ℝ u w).aestronglyMeasurable.mul
          hgs.continuous.aestronglyMeasurable
      · by_cases hx : x ∈ tsupport g
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)
        · simp [hzero x hx]
    · exact hint _ (hg'c w) (hzero' w)
    · exact hint _ hgs.continuous hzero
    · intro x hx
      exact ((hu x (hgΩ hx)).differentiableAt (hΩ.mem_nhds (hgΩ hx))).restrictScalars ℝ
    · intro x _
      exact hgd x
  have hlin : ∀ x, fderiv ℝ u x (I • v) * g x = I * (fderiv ℝ u x v * g x) := by
    intro x
    by_cases hx : x ∈ tsupport g
    · have hux : DifferentiableAt ℂ u x :=
        (hu x (hgΩ hx)).differentiableAt (hΩ.mem_nhds (hgΩ hx))
      rw [hux.fderiv_restrictScalars (𝕜 := ℝ)]
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
      ring
    · simp [hzero x hx]
  have hΩ0 : ∀ x, x ∉ Ω → u x * dbarDir g x v = 0 := by
    intro x hx
    have hx' : x ∉ tsupport g := fun h => hx (hgΩ h)
    simp [dbarDir, fderiv_of_notMem_tsupport ℝ hx']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hΩ0]
  have e1 : (fun x => u x * dbarDir g x v) =
      fun x => u x * fderiv ℝ g x (I • v) - I * (u x * fderiv ℝ g x v) := by
    funext x; simp only [dbarDir]; ring
  rw [e1, integral_sub (hint _ (hg'c _) (hzero' _)) ((hint _ (hg'c _) (hzero' _)).const_mul I),
    integral_const_mul, hibp (I • v), hibp v]
  simp only [hlin]
  rw [integral_const_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.C
