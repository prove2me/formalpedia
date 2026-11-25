-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.cMeasInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:14.63793+00:00
-- url     : https://prove2.me/submissions/e003c964-c98b-495d-a6b4-6e328c033b6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
private theorem continuous_cpt_apply (y0 : Frame X.Ψ r) : Continuous fun z => cpt X y0 z := by
  unfold ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ReciprocityTheory.ChartRestriction.G.FD.rmul ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat
    ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  refine Continuous.matrix_mul continuous_const ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · first
      | fun_prop
      | exact (EuclideanSpace.proj _).continuous
  · exact continuous_const
  · exact continuous_const
private theorem real_invariance_of_measInvStatement (hM : MeasInvStatement (E := E)) {y0 y1 : Frame X.Ψ r}
    (h0 : IsOrth X y0) (h1 : IsOrth X y1) (g : Frame X.Ψ r → ℝ) (hg : Measurable g)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, g (rmul x b) = g x) :
    ∫ z, g (cpt X y0 z) ∂muF X y0 = ∫ z, g (cpt X y1 z) ∂muF X y1 := by
  have hm0 : Measurable fun z => g (cpt X y0 z) := hg.comp (continuous_cpt_apply y0).measurable
  have hm1 : Measurable fun z => g (cpt X y1 z) := hg.comp (continuous_cpt_apply y1).measurable
  have hpos : ∫⁻ z, ENNReal.ofReal (g (cpt X y0 z)) ∂muF X y0 =
      ∫⁻ z, ENNReal.ofReal (g (cpt X y1 z)) ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (g x)) (ENNReal.measurable_ofReal.comp hg)
      (fun x hx b hb => by simp only [hB x hx b hb])
  have hneg : ∫⁻ z, ENNReal.ofReal (-g (cpt X y0 z)) ∂muF X y0 =
      ∫⁻ z, ENNReal.ofReal (-g (cpt X y1 z)) ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (-g x)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun x hx b hb => by simp only [hB x hx b hb])
  have hn : ∫⁻ z, ‖g (cpt X y0 z)‖ₑ ∂muF X y0 = ∫⁻ z, ‖g (cpt X y1 z)‖ₑ ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ‖g x‖ₑ) hg.enorm (fun x hx b hb => by simp only [hB x hx b hb])
  by_cases hi : Integrable (fun z => g (cpt X y0 z)) (muF X y0)
  · have hi' : Integrable (fun z => g (cpt X y1 z)) (muF X y1) := by
      refine ⟨hm1.aestronglyMeasurable, ?_⟩
      have h2 := hi.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [← hn]
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi', hpos, hneg]
  · have hi' : ¬ Integrable (fun z => g (cpt X y1 z)) (muF X y1) := by
      intro h
      refine hi ⟨hm0.aestronglyMeasurable, ?_⟩
      have h2 := h.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [hn]
    rw [integral_undef hi, integral_undef hi']
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
theorem _root_.solution (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) {x0' : Frame X.Ψ r}
    (hx0' : IsOrth X x0') (ψ : Frame X.Ψ r → ℂ) (hψ : Measurable ψ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫ z, ψ (cpt X x0 z) ∂muF X x0 = ∫ z, ψ (cpt X x0' z) ∂muF X x0' := by
  have hm0 : Measurable fun z => ψ (cpt X x0 z) := hψ.comp (continuous_cpt_apply x0).measurable
  have hm1 : Measurable fun z => ψ (cpt X x0' z) := hψ.comp (continuous_cpt_apply x0').measurable
  have hn : ∫⁻ z, ‖ψ (cpt X x0 z)‖ₑ ∂muF X x0 = ∫⁻ z, ‖ψ (cpt X x0' z)‖ₑ ∂muF X x0' :=
    hM r X x0 x0' hx0 hx0' (fun x => ‖ψ x‖ₑ) hψ.enorm (fun x hx b hb => by simp only [hB x hx b hb])
  by_cases hi : Integrable (fun z => ψ (cpt X x0 z)) (muF X x0)
  · have hi' : Integrable (fun z => ψ (cpt X x0' z)) (muF X x0') := by
      refine ⟨hm1.aestronglyMeasurable, ?_⟩
      have h2 := hi.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [← hn]
    apply Complex.ext
    · have e0 := Complex.reCLM.integral_comp_comm hi
      have e1 := Complex.reCLM.integral_comp_comm hi'
      simp only [Complex.reCLM_apply] at e0 e1
      rw [← e0, ← e1]
      exact real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).re) (Complex.measurable_re.comp hψ)
        (fun x hx b hb => by simp only [hB x hx b hb])
    · have e0 := Complex.imCLM.integral_comp_comm hi
      have e1 := Complex.imCLM.integral_comp_comm hi'
      simp only [Complex.imCLM_apply] at e0 e1
      rw [← e0, ← e1]
      exact real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).im) (Complex.measurable_im.comp hψ)
        (fun x hx b hb => by simp only [hB x hx b hb])
  · have hi' : ¬ Integrable (fun z => ψ (cpt X x0' z)) (muF X x0') := by
      intro h
      refine hi ⟨hm0.aestronglyMeasurable, ?_⟩
      have h2 := h.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [hn]
    rw [integral_undef hi, integral_undef hi']
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
