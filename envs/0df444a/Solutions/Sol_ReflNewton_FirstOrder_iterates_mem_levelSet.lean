-- Prove2me | solution 1 for ReflNewton.FirstOrder.iterates_mem_levelSet
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:27:20.038642+00:00
-- url     : https://prove2.me/submissions/e030160a-4bbd-44ad-8f99-3f017f6ddd04

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_FirstOrder_Setting
open Filter Topology

namespace Aux_ReflNewton_levelSet
open ReflNewton.FirstOrder

theorem reflectCoord_id (a b : EReal) (ha : a ≠ ⊤) (hb : b ≠ ⊥) (y : ℝ)
    (h1 : a < (y : EReal)) (h2 : (y : EReal) < b) : reflectCoord a b y = y := by
  unfold reflectCoord
  by_cases haB : a = ⊥
  · rw [if_pos haB]
    by_cases hbT : b = ⊤
    · rw [if_pos hbT]
    · rw [if_neg hbT, if_pos]
      have : (y : EReal) < ((b.toReal : ℝ) : EReal) := by rwa [EReal.coe_toReal hbT hb]
      exact (EReal.coe_lt_coe_iff.mp this).le
  · rw [if_neg haB]
    by_cases hbT : b = ⊤
    · rw [if_pos hbT, if_pos]
      have : ((a.toReal : ℝ) : EReal) < (y : EReal) := by rwa [EReal.coe_toReal ha haB]
      exact (EReal.coe_lt_coe_iff.mp this).le
    · rw [if_neg hbT]
      have ha' : a.toReal < y := by
        have : ((a.toReal : ℝ) : EReal) < (y : EReal) := by rwa [EReal.coe_toReal ha haB]
        exact EReal.coe_lt_coe_iff.mp this
      have hb' : y < b.toReal := by
        have : (y : EReal) < ((b.toReal : ℝ) : EReal) := by rwa [EReal.coe_toReal hbT hb]
        exact EReal.coe_lt_coe_iff.mp this
      simp only
      have hP : 0 < 2 * (b.toReal - a.toReal) := by linarith
      have habs : |y - a.toReal| = y - a.toReal := abs_of_pos (by linarith)
      rw [habs]
      have hlt : (y - a.toReal) / (2 * (b.toReal - a.toReal)) < 1 := by
        rw [div_lt_one hP]; linarith
      have hnn : 0 ≤ (y - a.toReal) / (2 * (b.toReal - a.toReal)) := div_nonneg (by linarith) hP.le
      rw [Int.fract_eq_self.mpr ⟨hnn, hlt⟩, mul_div_cancel₀ _ hP.ne']
      rw [min_eq_left (by linarith)]
      ring

theorem reflect_id {n : ℕ} (l u : Fin n → EReal) (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥)
    (y : E n) (hy : y ∈ intBox l u) : reflect l u y = y := by
  unfold reflect
  ext i
  simp only [PiLp.toLp_apply]
  exact reflectCoord_id _ _ (hl i) (hu i) _ (hy i).1 (hy i).2

end Aux_ReflNewton_levelSet

open ReflNewton.FirstOrder Aux_ReflNewton_levelSet in
theorem solution
    {n : ℕ} (l u : Fin n → EReal) (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : E n → ℝ) (D : Set (E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (σl σu ρ : ℝ) (hσl : 0 < σl) (hσlu : σl < σu) (hσu : σu < 1) (hρ : 0 < ρ)
    (x s : ℕ → E n) (α : ℕ → ℝ) (hrun : IsIRRun l u f σl σu ρ x s α) :
    ∀ k, x k ∈ LewisTorczon.BoundPS.levelSet l u f (x 0) ∧ f (x (k + 1)) < f (x k) := by
  have hbox : ∀ y, y ∈ intBox l u → y ∈ LewisTorczon.BoundPS.box l u := fun y hy i =>
    ⟨(hy i).1.le, (hy i).2.le⟩
  have hint : ∀ k, x k ∈ intBox l u := by
    intro k
    induction k with
    | zero => exact hrun.1
    | succ k ih =>
      obtain ⟨-, -, hmem, -, -, hx⟩ := hrun.2 k
      rw [hx]; exact hmem
  -- descent: ⟪∇f(x k), s k⟫ ≤ 0
  have hdesc : ∀ k, inner ℝ (gradient f (x k)) (s k) ≤ 0 := by
    intro k
    obtain ⟨hdd, -⟩ := hrun.2 k
    obtain ⟨ε, hε, hdec⟩ := hdd
    set y := x k
    set d := s k
    have hyD : y ∈ D := hFD (hbox y (hint k))
    have hdiff : DifferentiableAt ℝ f y :=
      (hf.differentiableOn (by norm_num)).differentiableAt (hDo.mem_nhds hyD)
    have hline : HasDerivAt (fun t : ℝ => f (y + t • d)) (fderiv ℝ f y d) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => y + t • d) d 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add y
      have h2 : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • d) := by
        rw [zero_smul, add_zero]; exact hdiff.hasFDerivAt
      exact h2.comp_hasDerivAt 0 h1
    have hgrad : fderiv ℝ f y d = inner ℝ (gradient f y) d := by
      rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]
    rw [← hgrad]
    by_contra hpos
    push_neg at hpos
    -- eventually the line stays in the interior box
    have hevbox : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • d ∈ intBox l u := by
      have : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), l i < (((y + t • d) i : ℝ) : EReal) ∧
          (((y + t • d) i : ℝ) : EReal) < u i := by
        intro i
        have hc : Tendsto (fun t : ℝ => (((y + t • d) i : ℝ) : EReal)) (𝓝 0) (𝓝 ((y i : ℝ) : EReal)) := by
          have : Continuous (fun t : ℝ => (((y + t • d) i : ℝ) : EReal)) := by
            refine continuous_coe_real_ereal.comp ?_
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            fun_prop
          have h0 := this.tendsto 0
          simpa using h0
        exact (hc.eventually (Ioo_mem_nhds (hint k i).1 (hint k i).2)).mono fun t ht => ht
      exact (eventually_all.mpr this).mono fun t ht i => ht i
    -- slope tends to the derivative
    have hslope := (hasDerivAt_iff_tendsto_slope.mp hline).mono_left
      (nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => ne_of_gt ht))
    have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope (fun t : ℝ => f (y + t • d)) 0 t :=
      hslope.eventually (lt_mem_nhds hpos)
    have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (y + t • d) < f y := by
      have hε' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε :=
        eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hε)
      filter_upwards [hε', self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hevbox]
        with t ht1 ht2 ht3
      have := hdec t ht2 ht1
      unfold reflPath at this
      rw [reflect_id l u hl hu _ ht3, add_sub_cancel] at this
      exact this
    obtain ⟨t, ht1, ht2, ht3⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
    rw [slope_def_field] at ht1
    simp only [zero_smul, add_zero, sub_zero] at ht1
    have ht3' : (0 : ℝ) < t := ht3
    have : 0 < f (y + t • d) - f y := by
      have := mul_pos ht1 ht3'
      rwa [div_mul_cancel₀ _ ht3'.ne'] at this
    linarith
  have hdec : ∀ k, f (x (k + 1)) < f (x k) := by
    intro k
    obtain ⟨-, hα, -, h34, -, -⟩ := hrun.2 k
    unfold cond34 at h34
    have h1 := hdesc k
    have h2 : min (hq f (x k) (s k)) 0 ≤ 0 := min_le_right _ _
    have h3 : α k * inner ℝ (gradient f (x k)) (s k) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα.le h1
    have h4 : 1 / 2 * α k ^ 2 * min (hq f (x k) (s k)) 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
    nlinarith
  intro k
  refine ⟨⟨hbox _ (hint k), ?_⟩, hdec k⟩
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (hdec k).le.trans ih
