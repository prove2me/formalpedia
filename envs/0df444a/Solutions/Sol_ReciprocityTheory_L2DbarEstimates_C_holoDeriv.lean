-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holoDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:22:22.461822+00:00
-- url     : https://prove2.me/submissions/cfa45e0e-f6de-48cf-bea0-0754027aeae2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExistsClmOfI
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_exists_clm_of_I
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open Metric Set Filter Topology Complex
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : HoloDerivStatement := by
  intro n Ω f hΩ hf v x hx
  have hs : ContDiffOn ℝ ∞ f Ω := holoSmooth n Ω f hΩ hf
  have hxn : Ω ∈ 𝓝 x := hΩ.mem_nhds hx
  have hloc : ∀ᶠ y in 𝓝 x, ∀ u : V n, fderiv ℝ f y u = fderiv ℂ f y u := by
    filter_upwards [hxn] with y hy u
    rw [((hf y hy).differentiableAt (hΩ.mem_nhds hy)).fderiv_restrictScalars ℝ]
    rfl
  have hD2 : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hs).2.contDiffAt hxn
  have hDd : DifferentiableAt ℝ (fderiv ℝ f) x := hD2.differentiableAt (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    ((contDiffOn_infty.1 hs 2).contDiffAt hxn).isSymmSndFDerivAt (by simp)
  have hder : ∀ u : V n, HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) x := by
    intro u
    simpa using hDd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have hI : ∀ w : V n, fderiv ℝ (fderiv ℝ f) x v (I • w) = I * fderiv ℝ (fderiv ℝ f) x v w := by
    intro w
    have hev : (fun y => fderiv ℝ f y (I • w)) =ᶠ[𝓝 x] fun y => I * fderiv ℝ f y w := by
      filter_upwards [hloc] with y hy
      rw [hy, hy, map_smul, smul_eq_mul]
    have h2 : HasFDerivAt (fun y => I * fderiv ℝ f y w) (I • (fderiv ℝ (fderiv ℝ f) x).flip w) x :=
      (hder w).const_mul I
    have h3 := ((hder (I • w)).congr_of_eventuallyEq hev.symm).unique h2
    have h4 := congrArg (fun L : V n →L[ℝ] ℂ => L v) h3
    simpa using h4
  have hA : ∀ w : V n, (fderiv ℝ (fderiv ℝ f) x).flip v (I • w) =
      I * (fderiv ℝ (fderiv ℝ f) x).flip v w := by
    intro w
    simp only [ContinuousLinearMap.flip_apply]
    rw [hsymm (I • w) v, hI w, hsymm w v]
  obtain ⟨gC, hgC⟩ := exists_clm_of_I _ hA
  have hev2 : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x] fun y => fderiv ℝ f y v := by
    filter_upwards [hloc] with y hy
    exact (hy v).symm
  exact ((hasFDerivAt_of_restrictScalars ℝ (hder v) hgC).congr_of_eventuallyEq hev2).differentiableAt.differentiableWithinAt
end ReciprocityTheory.L2DbarEstimates.C
