-- Prove2me | solution 1 for ReciprocityTheory.AnForm.fderiv_fderiv_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:45.831857+00:00
-- url     : https://prove2.me/submissions/a9f22d9c-b879-4cb5-a6ea-7d9e6f0528b0

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution (h h' h'' : ℝ → ℝ) (z : Fin 1 → ℂ)
    (hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' (h'' (‖z 0‖ ^ 2)) (‖z 0‖ ^ 2)) (w : Fin 1 → ℂ) :
    fderiv ℝ (fderiv ℝ fun y : Fin 1 → ℂ => h (‖y 0‖ ^ 2)) z w w =
      h'' (‖z 0‖ ^ 2) * (2 * inner ℝ (z 0) (w 0)) ^ 2 + h' (‖z 0‖ ^ 2) * (2 * ‖w 0‖ ^ 2) := by
  set p0 : (Fin 1 → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj 0 with hp0
  set q : (Fin 1 → ℂ) → ℝ := fun y => ‖y 0‖ ^ 2 with hqdef
  set B : (Fin 1 → ℂ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
    (2 : ℝ) • ((ContinuousLinearMap.compL ℝ (Fin 1 → ℂ) ℂ ℝ).flip p0).comp
      ((innerSL ℝ).comp p0) with hBdef
  have hB : ∀ y v, B y v = 2 * inner ℝ (y 0) (v 0) := by
    intro y v; simp [hBdef, hp0]
  have hq : ∀ y, HasFDerivAt q (B y) y := by
    intro y
    have h1 := (hasStrictFDerivAt_norm_sq (y 0)).hasFDerivAt.comp y p0.hasFDerivAt
    have hBy : B y = (2 • innerSL ℝ (y 0)).comp p0 := by
      ext v; simp [hB, hp0]; ring
    rw [hBy]
    exact h1
  have hqc : Continuous q := by rw [hqdef]; fun_prop
  have hev : ∀ᶠ y in 𝓝 z, HasDerivAt h (h' (q y)) (q y) :=
    hqc.continuousAt.tendsto.eventually hd
  have hfd : fderiv ℝ (fun y => h (q y)) =ᶠ[𝓝 z] fun y => h' (q y) • B y := by
    filter_upwards [hev] with y hy
    exact (hy.comp_hasFDerivAt y (hq y)).fderiv
  change fderiv ℝ (fderiv ℝ fun y => h (q y)) z w w = _
  rw [hfd.fderiv_eq]
  have hc : HasFDerivAt (fun y => h' (q y)) (h'' (q z) • B z) z :=
    hd2.comp_hasFDerivAt z (hq z)
  rw [HasFDerivAt.fderiv (f := fun y => h' (q y) • B y) (hc.smul B.hasFDerivAt)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hB, real_inner_self_eq_norm_sq]
  simp only [hqdef]
  ring
end ReciprocityTheory.AnForm
