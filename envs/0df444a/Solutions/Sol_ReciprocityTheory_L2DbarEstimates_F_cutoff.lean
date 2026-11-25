-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:53:47.853927+00:00
-- url     : https://prove2.me/submissions/98b7fe45-1a6c-4c22-b85d-3572066bb4e0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_norm_sq_le_two_form_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_pt_tri
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_weighted_add_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ofReal_lin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_lint_lin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_zero_off
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_smoothR_w
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_SmoothR_cut_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_aemeasurable_weighted_two_form
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_S_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_aem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_aesmS
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_aesmW
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_d_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_lint_tri
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ptF
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ptS
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ptW
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_locL2_of_weighted_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_two_form_sq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMA : MultAdjStatement n M) (hMS : MultSStatement n M) :
    CutoffStatement n M := by
  intro z hz e ph ψ he hph hψ hcut hcpt f w σ hf hw hσ hadj hS
  obtain ⟨hW1, hW2⟩ := cut_smoothR_w n z ph ψ hph hψ
  have cW1 := SmoothR.cut_continuous n z hz _ hW1
  have cW2 := SmoothR.cut_continuous n z hz _ hW2
  have cph := SmoothR.cut_continuous n z hz _ hph
  have hE : ∀ x, w1 ph ψ x - w2 ph ψ x = -ψ x := fun x => by simp only [w1, w2]; ring
  have cE : Continuous (fun x => w1 ph ψ x - w2 ph ψ x) := cW1.sub cW2
  choose η hηT hη01 hη1 hηD using hcut
  have hcont : ∀ ν, Continuous (η ν) := fun ν => SmoothR.cut_continuous n z hz _ (hηT ν).1
  have hdc : ∀ ν j, Continuous (d n z j (fun y => (η ν y : ℂ))) := fun ν j =>
    Smooth.continuous n z hz _ (Smooth.d n z j _ (hηT ν).1)
  have hdbc : ∀ ν j, Continuous (db n z j (fun y => (η ν y : ℂ))) := fun ν j =>
    Smooth.continuous n z hz _ (Smooth.db n z j _ (hηT ν).1)

  have hLf : LocalL2Isometry (vol n z) f := locL2_of_weighted_bound _ f (fun x => ‖f x‖ ^ 2) (w2 ph ψ) 1 zero_le_one cW2
    hf.1 (fun x => by simp) hf.2
  have hLσ : LocalL2Isometry (vol n z) σ := locL2_of_weighted_bound _ σ (fun x => sq2 n (σ x)) ph 2 zero_le_two cph
    hσ.1 (fun x => norm_sq_le_two_form_sq n (σ x)) hσ.2

  set b1 : M → ℝ≥0∞ := fun x => ENNReal.ofReal (‖f x‖ ^ 2 * Real.exp (-w2 ph ψ x)) with hb1
  set b2 : M → ℝ≥0∞ := fun x => ENNReal.ofReal 2 * ENNReal.ofReal (‖w x‖ ^ 2 * Real.exp (-w1 ph ψ x)) +
    ENNReal.ofReal 2 * b1 x with hb2
  set b3 : M → ℝ≥0∞ := fun x => ENNReal.ofReal 2 * ENNReal.ofReal (sq2 n (σ x) * Real.exp (-ph x)) +
    ENNReal.ofReal 4 * b1 x with hb3
  have hb1f : ∫⁻ x, b1 x ∂vol n z < ⊤ := hf.2
  have hb2f : ∫⁻ x, b2 x ∂vol n z < ⊤ :=
    cut_lint_lin _ _ _ (cut_aem _ w hw.1 _ cW1) 2 2 hw.2 hb1f
  have hb3f : ∫⁻ x, b3 x ∂vol n z < ⊤ :=
    cut_lint_lin _ _ _ (aemeasurable_weighted_two_form n _ σ hσ.1 _ cph) 2 4 hσ.2 hb1f
  have bF : ∀ (c : ℝ), |c| ≤ 1 → ∀ x,
      ENNReal.ofReal (‖(c : ℂ) • f x‖ ^ 2 * Real.exp (-w2 ph ψ x)) ≤ b1 x := fun c hc x =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (cut_ptF c hc (f x)) (Real.exp_pos _).le)
  have bW : ∀ ν (c : ℝ), |c| ≤ 1 → ∀ x,
      ENNReal.ofReal (‖(c : ℂ) * w x - (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) *
        ∑ j, d n z j (fun y => (η ν y : ℂ)) x * f x j‖ ^ 2 * Real.exp (-w1 ph ψ x)) ≤ b2 x := by
    intro ν c hc x
    rw [hE x]
    exact cut_ofReal_lin 2 2 _ _ _ zero_le_two zero_le_two (by positivity) (by positivity)
      (cut_ptW c hc (w x) _ (‖f x‖ ^ 2) _ (ph x) (ψ x) (cut_S_bound n z (η ν) (f x) x)
        (hηD ν x) (sq_nonneg _))
  have bS : ∀ ν (c : ℝ), |c| ≤ 1 → ∀ x,
      ENNReal.ofReal (sq2 n (fun j k => (c : ℂ) * σ x j k +
        wedge (fun i => db n z i (fun y => (η ν y : ℂ)) x) (fun i => f x i) j k) *
          Real.exp (-ph x)) ≤ b3 x := by
    intro ν c hc x
    exact cut_ofReal_lin 2 4 _ _ _ zero_le_two zero_le_four
      (mul_nonneg (two_form_sq_nonneg n _) (Real.exp_pos _).le) (by positivity)
      (cut_ptS c hc (σ x) _ _ _ (‖f x‖ ^ 2) (ph x) (ψ x) rfl (EuclideanSpace.norm_sq_eq (f x)).symm
        (hηD ν x))
  have habs : ∀ ν x, |η ν x| ≤ 1 := fun ν x =>
    abs_le.2 ⟨by linarith [(hη01 ν x).1], (hη01 ν x).2⟩
  have habs1 : ∀ ν x, |η ν x - 1| ≤ 1 := fun ν x =>
    abs_le.2 ⟨by linarith [(hη01 ν x).1], by linarith [(hη01 ν x).2]⟩

  have hmF : ∀ ν, MemWeightedL2OneForm n z (fun x => (η ν x : ℂ) • f x) (w2 ph ψ) := fun ν =>
    ⟨(Complex.continuous_ofReal.comp (hcont ν)).aestronglyMeasurable.smul hf.1,
      (lintegral_mono fun x => bF _ (habs ν x) x).trans_lt hb1f⟩
  have hmW : ∀ ν, MemWeightedL2 n z (cutW n z ph ψ (η ν) f w) (w1 ph ψ) := fun ν =>
    ⟨cut_aesmW n z _ ph ψ (η ν) (η ν) f w (hcont ν) cE (hdc ν) hf.1 hw.1,
      (lintegral_mono fun x => bW ν _ (habs ν x) x).trans_lt hb2f⟩
  have hmS : ∀ ν, MemWeightedL2TwoForm n z (cutS n z (η ν) f σ) ph := fun ν =>
    ⟨cut_aesmS n z _ (η ν) (η ν) f σ (hcont ν) (hdbc ν) hf.1 hσ.1,
      (lintegral_mono fun x => bS ν _ (habs ν x) x).trans_lt hb3f⟩
  have hA : ∀ ν, IsWeakAdj n z (w1 ph ψ) (w2 ph ψ) (fun x => (η ν x : ℂ) • f x)
      (cutW n z ph ψ (η ν) f w) := fun ν =>
    hMA z hz _ _ (η ν) f w hW1 hW2 (hηT ν).1 hf hw hadj
  have hSS : ∀ ν, IsWeakS n z (fun x => (η ν x : ℂ) • f x) (cutS n z (η ν) f σ) := fun ν =>
    hMS z hz (η ν) f σ (hηT ν).1 hLf hLσ hS
  have hcF : ∀ ν, HasCompactSupport (fun x => (η ν x : ℂ) • f x) := fun ν =>
    (hηT ν).2.mono' fun x hx => by
      by_contra h
      exact hx (by simp [(cut_zero_off n z (η ν) x h).1])
  have hcW : ∀ ν, HasCompactSupport (cutW n z ph ψ (η ν) f w) := fun ν =>
    (hηT ν).2.mono' fun x hx => by
      by_contra h
      obtain ⟨h0, h1, -⟩ := cut_zero_off n z (η ν) x h
      exact hx (by simp [cutW, h0, h1])
  have hcS : ∀ ν, HasCompactSupport (cutS n z (η ν) f σ) := fun ν =>
    (hηT ν).2.mono' fun x hx => by
      by_contra h
      obtain ⟨h0, -, h2⟩ := cut_zero_off n z (η ν) x h
      refine hx ?_
      funext j k
      simp [cutS, wedge, h0, h2]

  have eF : ∀ ν x, (η ν x : ℂ) • f x - f x = ((η ν x - 1 : ℝ) : ℂ) • f x := fun ν x => by
    push_cast; rw [sub_smul, one_smul]
  have eW : ∀ ν x, cutW n z ph ψ (η ν) f w x - w x = ((η ν x - 1 : ℝ) : ℂ) * w x -
      (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) * ∑ j, d n z j (fun y => (η ν y : ℂ)) x * f x j :=
    fun ν x => by simp only [cutW]; push_cast; ring
  have eS : ∀ ν x, cutS n z (η ν) f σ x - σ x = fun j k => ((η ν x - 1 : ℝ) : ℂ) * σ x j k +
      wedge (fun i => db n z i (fun y => (η ν y : ℂ)) x) (fun i => f x i) j k :=
    fun ν x => by funext j k; simp only [cutS, Pi.sub_apply]; push_cast; ring
  have hvan : ∀ x, ∀ᶠ ν : ℕ in atTop, (η ν x = 1 ∧ (∀ j, d n z j (fun y => (η ν y : ℂ)) x = 0) ∧
      ∀ j, db n z j (fun y => (η ν y : ℂ)) x = 0) := by
    intro x
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (e x)] with ν hν
    have hU : IsOpen {y | e y < (ν : ℝ)} := isOpen_lt he continuous_const
    have h1 : ∀ y ∈ {y | e y < (ν : ℝ)}, η ν y = 1 := fun y hy => hη1 ν y (le_of_lt hy)
    exact ⟨h1 x hν, fun j => (cut_d_eq_zero n z hz j (η ν) _ hU h1 x hν).1,
      fun j => (cut_d_eq_zero n z hz j (η ν) _ hU h1 x hν).2⟩
  have tF : Tendsto (fun ν : ℕ => ∫⁻ x, ENNReal.ofReal (‖(η ν x : ℂ) • f x - f x‖ ^ 2 *
      Real.exp (-w2 ph ψ x)) ∂vol n z) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := vol n z) (f := fun _ => 0)
      (F := fun ν x => ENNReal.ofReal (‖(η ν x : ℂ) • f x - f x‖ ^ 2 * Real.exp (-w2 ph ψ x))) b1
      (fun ν => cut_aem _ (fun x => (η ν x : ℂ) • f x - f x) (((Complex.continuous_ofReal.comp (hcont ν)).aestronglyMeasurable.smul
        hf.1).sub hf.1) _ cW2)
      (fun ν => ae_of_all _ fun x => by dsimp only; rw [eF]; exact bF _ (habs1 ν x) x) hb1f.ne
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ((hvan x).mono fun ν h => by simp [h.1]))
    simpa only [lintegral_zero] using this
  have tW : Tendsto (fun ν : ℕ => ∫⁻ x, ENNReal.ofReal (‖cutW n z ph ψ (η ν) f w x - w x‖ ^ 2 *
      Real.exp (-w1 ph ψ x)) ∂vol n z) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := vol n z) (f := fun _ => 0)
      (F := fun ν x => ENNReal.ofReal (‖cutW n z ph ψ (η ν) f w x - w x‖ ^ 2 *
        Real.exp (-w1 ph ψ x))) b2
      (fun ν => cut_aem _ (fun x => cutW n z ph ψ (η ν) f w x - w x) ((cut_aesmW n z _ ph ψ (η ν) (η ν) f w (hcont ν) cE (hdc ν) hf.1
        hw.1).sub hw.1) _ cW1)
      (fun ν => ae_of_all _ fun x => by dsimp only; rw [eW]; exact bW ν _ (habs1 ν x) x) hb2f.ne
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ((hvan x).mono fun ν h => by
        simp [cutW, h.1, h.2.1]))
    simpa only [lintegral_zero] using this
  have tS : Tendsto (fun ν : ℕ => ∫⁻ x, ENNReal.ofReal (sq2 n (cutS n z (η ν) f σ x - σ x) *
      Real.exp (-ph x)) ∂vol n z) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := vol n z) (f := fun _ => 0)
      (F := fun ν x => ENNReal.ofReal (sq2 n (cutS n z (η ν) f σ x - σ x) * Real.exp (-ph x))) b3
      (fun ν => aemeasurable_weighted_two_form n _ (fun x => cutS n z (η ν) f σ x - σ x) ((cut_aesmS n z _ (η ν) (η ν) f σ (hcont ν) (hdbc ν) hf.1
        hσ.1).sub hσ.1) _ cph)
      (fun ν => ae_of_all _ fun x => by dsimp only; rw [eS]; exact bS ν _ (habs1 ν x) x) hb3f.ne
      (ae_of_all _ fun x => tendsto_const_nhds.congr' ((hvan x).mono fun ν h => by
        have : cutS n z (η ν) f σ x - σ x = 0 := by
          funext j k; simp [cutS, wedge, h.1, h.2.2]
        dsimp only; rw [this]; simp [sq2]))
    simpa only [lintegral_zero] using this

  intro δ hδ
  set q : ℝ≥0∞ := min δ 1 / 4 with hq
  have hmin0 : min δ 1 ≠ 0 := (lt_min hδ one_pos).ne'
  have hq0 : 0 < q := ENNReal.div_pos hmin0 (by norm_num)
  have h4q : 4 * q ≤ δ := ENNReal.mul_div_le.trans (min_le_left _ _)
  have fin : ∀ a b : ℝ≥0∞, a < q → b < q → 2 * a + 2 * b < δ := by
    intro a b ha hb
    calc 2 * a + 2 * b < 2 * q + 2 * q :=
          ENNReal.add_lt_add (ENNReal.mul_lt_mul_right (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤) ha)
            (ENNReal.mul_lt_mul_right (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hb)
      _ = 4 * q := by ring
      _ ≤ δ := h4q
  obtain ⟨ν, hν1, hν2, hν3⟩ := (((tendsto_order.1 tF).2 q hq0).and
    (((tendsto_order.1 tW).2 q hq0).and ((tendsto_order.1 tS).2 q hq0))).exists
  obtain ⟨g, hg, hg1, hg2, hg3⟩ := hcpt _ _ _ (hmF ν) (hmW ν) (hmS ν) (hA ν) (hSS ν) (hcF ν)
    (hcW ν) (hcS ν) q hq0
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · unfold nV at hg1 ⊢
    refine lt_of_le_of_lt ?_ (fin _ _ hg1 hν1)
    refine cut_lint_tri _ _ _ _ (cut_aem _ (fun x => (η ν x : ℂ) • f x - f x)
      ((Complex.continuous_ofReal.comp (hcont ν)).aestronglyMeasurable.smul hf.1 |>.sub hf.1)
      _ cW2) fun x => ?_
    have := cut_pt_tri (g x - (η ν x : ℂ) • f x) ((η ν x : ℂ) • f x - f x) _
      (Real.exp_pos (-w2 ph ψ x)).le
    rwa [sub_add_sub_cancel] at this
  · unfold wint at hg2 ⊢
    refine lt_of_le_of_lt ?_ (fin _ _ hg2 hν2)
    refine cut_lint_tri _ _ _ _ (cut_aem _ (fun x => cutW n z ph ψ (η ν) f w x - w x)
      ((cut_aesmW n z _ ph ψ (η ν) (η ν) f w (hcont ν) cE (hdc ν) hf.1 hw.1).sub hw.1)
      _ cW1) fun x => ?_
    have := cut_pt_tri (tstar n z (w1 ph ψ) (w2 ph ψ) g x - cutW n z ph ψ (η ν) f w x)
      (cutW n z ph ψ (η ν) f w x - w x) _ (Real.exp_pos (-w1 ph ψ x)).le
    rwa [sub_add_sub_cancel] at this
  · unfold n2 at hg3 ⊢
    refine lt_of_le_of_lt ?_ (fin _ _ hg3 hν3)
    refine cut_lint_tri _ _ _ _ (aemeasurable_weighted_two_form n _ (fun x => cutS n z (η ν) f σ x - σ x)
      ((cut_aesmS n z _ (η ν) (η ν) f σ (hcont ν) (hdbc ν) hf.1 hσ.1).sub hσ.1)
      _ cph) fun x => ?_
    have := two_form_weighted_add_le n (sbar n z g x - cutS n z (η ν) f σ x)
      (cutS n z (η ν) f σ x - σ x) _ (Real.exp_pos (-ph x)).le
    rwa [sub_add_sub_cancel] at this
end ReciprocityTheory.L2DbarEstimates.F
