-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.near_smooth_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:42.716942+00:00
-- url     : https://prove2.me/submissions/b76f3f72-4de2-4393-bfda-583c9a553191

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_near_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holo_contDiffOn_complex
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
noncomputable section
private theorem contDiffOn_vsq_gv_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => vsq (gv g (e.symm y))) e.target := by
  unfold vsq gv
  refine ContDiffOn.sum fun l _ => ?_
  have hd : DifferentiableOn ℂ (g l ∘ e.symm) e.target := hg l e he
  have ho : IsOpen e.target := e.open_target
  have h0 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target :=
    C.holo_contDiffOn_complex ho hd
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l ∘ e.symm) e.target :=
    h0.restrict_scalars ℝ
  exact (contDiff_norm_sq ℝ).comp_contDiffOn h1
end
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) {p : ℕ} (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l))
    (hN : ∀ x, gv g x ≠ 0) (u : M → ℂ) (hu : Holo n z u) (i : Fin p) :
    Smooth n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) := by
  intro e he
  have hu' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ e.symm) e.target :=
    (C.holo_contDiffOn_complex e.open_target (hu e he)).restrict_scalars ℝ
  have hg' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i ∘ e.symm) e.target :=
    (C.holo_contDiffOn_complex e.open_target (hg i e he)).restrict_scalars ℝ
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (g i (e.symm y))) e.target :=
    Complex.conjCLE.contDiff.comp_contDiffOn hg'
  have hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (((vsq (gv g (e.symm y)))⁻¹ : ℝ) : ℂ))
      e.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_vsq_gv_comp_chart_symm n z g hg e he).inv
      fun y _ => (near_vsq_pos (gv g (e.symm y)) (hN (e.symm y))).ne')
  have hnum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y))) e.target := hu'.mul hc
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u (e.symm y) * (starRingEnd ℂ) (g i (e.symm y)) /
    ((vsq (gv g (e.symm y)) : ℝ) : ℂ)) e.target
  exact (hnum.mul hv).congr fun y _ => by simp [div_eq_mul_inv]
end ReciprocityTheory.L2DbarEstimates.H
