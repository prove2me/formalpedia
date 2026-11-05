-- Prove2me | solution 1 for PrimalDualPricing.Regret.proposition_1_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:57:29.510211+00:00
-- url     : https://prove2.me/submissions/2e93279d-23b9-4d23-af2f-b9ea4d53dff7

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Model
import Definitions.Def_PrimalDualPricing_Regret_FluidValue

open Set PrimalDualPricing.Regret

namespace PDP112

variable {M : ℕ} (μ : Model M) (m : Fin M)

lemma d_cont : ContinuousOn (μ.d m) (Icc 0 μ.pinf) := (μ.d_lip m).continuousOn

lemma dinv_mem {l : ℝ} (hl : l ∈ Icc (μ.d m μ.pinf) (μ.d m 0)) :
    μ.dinv m l ∈ Icc 0 μ.pinf := by
  obtain ⟨p, hp, hpl⟩ := intermediate_value_Icc' μ.pinf_pos.le (d_cont μ m) hl
  rw [← hpl, μ.dinv_d m p hp]; exact hp

lemma Lam_mem (z : ℝ) : μ.d m (μ.P m z) ∈ Icc (μ.d m μ.pinf) (μ.d m 0) := by
  have h := μ.P_mem m z
  have hA := (μ.d_strictAnti m).antitoneOn
  exact ⟨hA h ⟨μ.pinf_pos.le, le_rfl⟩ h.2, hA ⟨le_rfl, μ.pinf_pos.le⟩ h h.1⟩

/-- `Λ(z) = d(P z)` maximizes `λ ↦ r(λ) - λ z` on `I`. -/
lemma Lam_isMax (z : ℝ) :
    IsMaxOn (fun l => l * μ.dinv m l - l * z) (Icc (μ.d m μ.pinf) (μ.d m 0))
      (μ.d m (μ.P m z)) := by
  intro l hl
  have hp := dinv_mem μ m hl
  have h1 := μ.P_isMax m z _ hp
  rw [μ.d_dinv m l hl] at h1
  show l * μ.dinv m l - l * z ≤ μ.d m (μ.P m z) * μ.dinv m (μ.d m (μ.P m z))
    - μ.d m (μ.P m z) * z
  rw [μ.dinv_d m _ (μ.P_mem m z)]
  linarith

lemma Lam_opt (z l : ℝ) (hl : l ∈ Icc (μ.d m μ.pinf) (μ.d m 0)) :
    (l - μ.d m (μ.P m z)) * (μ.r' m (μ.d m (μ.P m z)) - z) ≤ 0 := by
  set I := Icc (μ.d m μ.pinf) (μ.d m 0)
  set L := μ.d m (μ.P m z)
  have hL := Lam_mem μ m z
  have hmax := (Lam_isMax μ m z).localize
  have hder : HasDerivWithinAt (fun l => l * μ.dinv m l - l * z) (μ.r' m L - z) I L := by
    exact ((μ.rev_hasDeriv m L hL).sub ((hasDerivWithinAt_id L I).mul_const z)).congr_deriv
      (by ring)
  have hcone : l - L ∈ posTangentConeAt I L := by
    apply mem_posTangentConeAt_of_segment_subset
    simpa using (convex_Icc _ _).segment_subset hL hl
  have := hmax.hasFDerivWithinAt_nonpos hder.hasFDerivWithinAt hcone
  simpa [mul_comm] using this

lemma rprime_strong {a b : ℝ} (ha : a ∈ Icc (μ.d m μ.pinf) (μ.d m 0))
    (hb : b ∈ Icc (μ.d m μ.pinf) (μ.d m 0)) :
    μ.M₃ * (a - b) ^ 2 ≤ -((μ.r' m a - μ.r' m b) * (a - b)) := by
  set I := Icc (μ.d m μ.pinf) (μ.d m 0)
  have hanti : AntitoneOn (fun x => μ.r' m x + μ.M₃ * x) I := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun x => μ.r'' m x + μ.M₃)
    · intro x hx
      exact ((μ.rev'_hasDeriv m x hx).continuousWithinAt).add
        (continuousWithinAt_const.mul continuousWithinAt_id)
    · intro x hx
      have h1 := (μ.rev'_hasDeriv m x (interior_subset hx)).mono interior_subset
      have h2 := ((hasDerivWithinAt_id x (interior I)).const_mul μ.M₃)
      exact (h1.add h2).congr_deriv (by ring)
    · intro x hx
      have := (μ.rev''_bounds m x (interior_subset hx)).1
      show μ.r'' m x + μ.M₃ ≤ 0
      linarith
  rcases le_total a b with hab | hab
  · have := hanti ha hb hab
    simp only at this
    nlinarith
  · have := hanti hb ha hab
    simp only at this
    nlinarith

lemma Lam_lip (z₁ z₂ : ℝ) :
    μ.M₃ * |μ.d m (μ.P m z₁) - μ.d m (μ.P m z₂)| ≤ |z₁ - z₂| := by
  set L₁ := μ.d m (μ.P m z₁)
  set L₂ := μ.d m (μ.P m z₂)
  have h1 := Lam_opt μ m z₁ L₂ (Lam_mem μ m z₂)
  have h2 := Lam_opt μ m z₂ L₁ (Lam_mem μ m z₁)
  have h3 := rprime_strong μ m (Lam_mem μ m z₁) (Lam_mem μ m z₂)
  have key : μ.M₃ * (L₁ - L₂) ^ 2 ≤ (L₂ - L₁) * (z₁ - z₂) := by nlinarith
  have hab : (L₂ - L₁) * (z₁ - z₂) ≤ |L₁ - L₂| * |z₁ - z₂| := by
    rw [← abs_sub_comm L₂ L₁, ← abs_mul]; exact le_abs_self _
  have hsq : (L₁ - L₂) ^ 2 = |L₁ - L₂| * |L₁ - L₂| := by rw [abs_mul_abs_self, sq]
  rw [hsq] at key
  rcases (abs_nonneg (L₁ - L₂)).eq_or_lt with h | h
  · rw [← h, mul_zero]; exact abs_nonneg _
  · have : μ.M₃ * |L₁ - L₂| * |L₁ - L₂| ≤ |z₁ - z₂| * |L₁ - L₂| := by nlinarith
    exact le_of_mul_le_mul_right this h

lemma P_dist (z₁ z₂ : ℝ) :
    |μ.P m z₁ - μ.P m z₂| ≤ ((Real.toNNReal μ.M₂ : ℝ) / μ.M₃) * |z₁ - z₂| := by
  have e1 := μ.dinv_d m _ (μ.P_mem m z₁)
  have e2 := μ.dinv_d m _ (μ.P_mem m z₂)
  have hd := (μ.dinv_lip m).dist_le_mul _ (Lam_mem μ m z₁) _ (Lam_mem μ m z₂)
  rw [e1, e2, Real.dist_eq, Real.dist_eq] at hd
  have hl := Lam_lip μ m z₁ z₂
  have hM3 := μ.M₃_pos
  have hK : (0 : ℝ) ≤ (Real.toNNReal μ.M₂ : ℝ) := NNReal.coe_nonneg _
  calc |μ.P m z₁ - μ.P m z₂| ≤ (Real.toNNReal μ.M₂ : ℝ)
        * |μ.d m (μ.P m z₁) - μ.d m (μ.P m z₂)| := hd
    _ ≤ (Real.toNNReal μ.M₂ : ℝ) * (|z₁ - z₂| / μ.M₃) := by
        apply mul_le_mul_of_nonneg_left _ hK
        rw [le_div_iff₀ hM3]; linarith
    _ = _ := by ring

lemma P_mono : Monotone (μ.P m) := by
  intro z₁ z₂ hz
  rcases hz.eq_or_lt with h | h
  · rw [h]
  by_contra hlt
  push Not at hlt
  have a1 := μ.P_isMax m z₁ _ (μ.P_mem m z₂)
  have a2 := μ.P_isMax m z₂ _ (μ.P_mem m z₁)
  have hd : μ.d m (μ.P m z₁) < μ.d m (μ.P m z₂) :=
    μ.d_strictAnti m (μ.P_mem m z₂) (μ.P_mem m z₁) hlt
  nlinarith

lemma Rm_eq (z : ℝ) : μ.Rm m z = μ.d m (μ.P m z) * (μ.P m z - z) := by
  unfold Model.Rm
  apply IsGreatest.csSup_eq
  refine ⟨⟨μ.P m z, μ.P_mem m z, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact μ.P_isMax m z p hp

lemma Rm_ge (z p : ℝ) (hp : p ∈ Icc 0 μ.pinf) : μ.d m p * (p - z) ≤ μ.Rm m z := by
  rw [Rm_eq]; exact μ.P_isMax m z p hp

end PDP112

open PDP112 in
theorem PDP112.prop112 {M : ℕ} (μ : Model M) (m : Fin M) :
    (Monotone (μ.P m) ∧ ∃ L : NNReal, LipschitzWith L (μ.P m)) ∧
    (Antitone (μ.Rm m) ∧ ConvexOn ℝ Set.univ (μ.Rm m) ∧
      ∀ z : ℝ, HasDerivAt (μ.Rm m) (-(μ.d m (μ.P m z))) z) := by
  have hM3 := μ.M₃_pos
  set K : ℝ := (Real.toNNReal μ.M₂ : ℝ) / μ.M₃ with hKdef
  have hK0 : 0 ≤ K := div_nonneg (NNReal.coe_nonneg _) hM3.le
  refine ⟨⟨P_mono μ m, ⟨Real.toNNReal K, ?_⟩⟩, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    exact P_dist μ m x y
  · intro z₁ z₂ hz
    have := Rm_ge μ m z₁ _ (μ.P_mem m z₂)
    rw [Rm_eq μ m z₂]
    have hd := μ.d_nonneg m (μ.P m z₂)
    nlinarith
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    set p := μ.P m (a * x + b * y)
    rw [Rm_eq μ m (a * x + b * y)]
    have h1 := Rm_ge μ m x p (μ.P_mem m _)
    have h2 := Rm_ge μ m y p (μ.P_mem m _)
    have e : μ.d m p * (p - (a * x + b * y))
        = a * (μ.d m p * (p - x)) + b * (μ.d m p * (p - y)) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · intro z
    set K2 : ℝ := (Real.toNNReal μ.M₂ : ℝ)
    have hK2 : 0 ≤ K2 := NNReal.coe_nonneg _
    -- quadratic remainder bound
    have hrem : ∀ w, |μ.Rm m w - μ.Rm m z - (w - z) * (-(μ.d m (μ.P m z)))|
        ≤ (K2 * K) * |w - z| ^ 2 := by
      intro w
      have lo := Rm_ge μ m w _ (μ.P_mem m z)
      have hi := Rm_ge μ m z _ (μ.P_mem m w)
      simp only [Rm_eq μ m] at lo hi ⊢
      have hdd : |μ.d m (μ.P m z) - μ.d m (μ.P m w)| ≤ K2 * |μ.P m z - μ.P m w| := by
        have := (μ.d_lip m).dist_le_mul _ (μ.P_mem m z) _ (μ.P_mem m w)
        rwa [Real.dist_eq, Real.dist_eq] at this
      have hpp := P_dist μ m z w
      have hdd2 : |μ.d m (μ.P m z) - μ.d m (μ.P m w)| ≤ K2 * K * |w - z| := by
        rw [abs_sub_comm w z]
        calc _ ≤ K2 * |μ.P m z - μ.P m w| := hdd
          _ ≤ K2 * (K * |z - w|) := mul_le_mul_of_nonneg_left hpp hK2
          _ = _ := by ring
      set E := μ.d m (μ.P m w) * (μ.P m w - w) - μ.d m (μ.P m z) * (μ.P m z - z)
        - (w - z) * -μ.d m (μ.P m z)
      have hE0 : 0 ≤ E := by simp only [E]; nlinarith
      have hE1 : E ≤ (w - z) * (μ.d m (μ.P m z) - μ.d m (μ.P m w)) := by
        simp only [E]; nlinarith
      have hE2 : (w - z) * (μ.d m (μ.P m z) - μ.d m (μ.P m w))
          ≤ |w - z| * |μ.d m (μ.P m z) - μ.d m (μ.P m w)| := by
        rw [← abs_mul]; exact le_abs_self _
      rw [abs_of_nonneg hE0]
      have := mul_le_mul_of_nonneg_left hdd2 (abs_nonneg (w - z))
      nlinarith
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hC : 0 < K2 * K + 1 := by positivity
    rw [Metric.eventually_nhds_iff]
    refine ⟨c / (K2 * K + 1), div_pos hc hC, fun w hw => ?_⟩
    rw [Real.dist_eq] at hw
    simp only [smul_eq_mul, Real.norm_eq_abs]
    have h1 := hrem w
    have h2 : (K2 * K) * |w - z| ^ 2 ≤ c * |w - z| := by
      have hw' : (K2 * K + 1) * |w - z| ≤ c := by
        rw [lt_div_iff₀ hC] at hw; linarith
      have := mul_le_mul_of_nonneg_left hw' (abs_nonneg (w - z))
      nlinarith [abs_nonneg (w - z), sq_nonneg (w - z)]
    linarith

namespace PDP14

open MeasureTheory PDP112

variable {M : ℕ} (μ : Model M)

noncomputable def clamp (x : ℝ) : ℝ := max 0 (min μ.pinf x)

lemma clamp_cont : Continuous (clamp μ) := continuous_const.max (continuous_const.min continuous_id)

lemma clamp_mem (x : ℝ) : clamp μ x ∈ Icc 0 μ.pinf :=
  ⟨le_max_left _ _, max_le μ.pinf_pos.le (min_le_left _ _)⟩

lemma clamp_eq {x : ℝ} (hx : x ∈ Icc 0 μ.pinf) : clamp μ x = x := by
  simp [clamp, min_eq_right hx.2, max_eq_right hx.1]

lemma dc_cont (m : Fin M) : Continuous (fun x => μ.d m (clamp μ x)) :=
  (d_cont μ m).comp_continuous (clamp_cont μ) (clamp_mem μ)

lemma ii_of_bound {f : ℝ → ℝ} (hf : Measurable f) (a b : ℝ) (hb : ∀ t, f t ∈ Icc a b) :
    IntervalIntegrable f volume 0 μ.T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le μ.T_pos.le]
  exact Integrable.of_mem_Icc a b hf.aemeasurable (ae_of_all _ hb)

/-- Derivative of the dual function. -/
lemma g_hasDeriv (z : ℝ) :
    HasDerivAt μ.dualFn (μ.c - μ.T * ∑ m, μ.d m (μ.P m z)) z := by
  have h1 : HasDerivAt (fun z => ∑ m, μ.Rm m z) (∑ m, -(μ.d m (μ.P m z))) z :=
    HasDerivAt.fun_sum (fun m _ => ((prop112 μ m).2.2.2 z))
  have h2 := ((hasDerivAt_id z).const_mul μ.c).add (h1.const_mul μ.T)
  unfold Model.dualFn
  exact h2.congr_deriv (by simp only [mul_one, Finset.sum_neg_distrib]; ring)

lemma kkt : μ.T * ∑ m, μ.d m (μ.P m μ.zstar) ≤ μ.c ∧
    μ.zstar * (μ.c - μ.T * ∑ m, μ.d m (μ.P m μ.zstar)) = 0 := by
  set g' := μ.c - μ.T * ∑ m, μ.d m (μ.P m μ.zstar)
  have hmin : IsLocalMinOn μ.dualFn (Ici 0) μ.zstar := by
    apply IsMinOn.localize
    intro z hz
    exact μ.zstar_isMin z hz
  have hd := (g_hasDeriv μ μ.zstar).hasDerivWithinAt (s := Ici 0)
  have hz0 := μ.zstar_nonneg
  have c1 : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) μ.zstar := by
    apply mem_posTangentConeAt_of_segment_subset
    intro x hx
    rw [segment_eq_Icc (by linarith)] at hx
    exact le_trans hz0 hx.1
  have c2 : (-μ.zstar) ∈ posTangentConeAt (Ici (0 : ℝ)) μ.zstar := by
    apply mem_posTangentConeAt_of_segment_subset
    intro x hx
    rw [show μ.zstar + -μ.zstar = 0 by ring, segment_symm, segment_eq_Icc hz0] at hx
    exact hx.1
  have e1 := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt c1
  have e2 := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt c2
  simp at e1 e2
  constructor
  · linarith
  · nlinarith

/-- The fluid value of the problem with demand `κ d` and inventory `κ c`. -/
lemma fluid_scaled (κ : ℝ) (hκ : 0 ≤ κ) :
    fluidValue (fun m p => κ * μ.d m p) μ.pinf (κ * μ.c) μ.T
      = κ * (μ.T * ∑ m, μ.pstar m * μ.d m (μ.pstar m)) := by
  obtain ⟨hfeas, hslack⟩ := kkt μ
  have hT := μ.T_pos
  have hz0 := μ.zstar_nonneg
  unfold fluidValue
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ m => μ.pstar m, ⟨measurable_const, fun t _ m => μ.P_mem m _, ?_⟩, ?_⟩
    · simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      rw [show ∑ m, μ.T * (κ * μ.d m (μ.pstar m))
          = κ * (μ.T * ∑ m, μ.d m (μ.P m μ.zstar)) from by
            rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
            simp only [Model.pstar]; ring]
      exact mul_le_mul_of_nonneg_left hfeas hκ
    · simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro m _; ring
  · rintro _ ⟨p, ⟨hpm, hpI, hpc⟩, rfl⟩
    simp only at hpc ⊢
    -- per-type bound
    have hA : ∀ m, ∫ t in (0 : ℝ)..μ.T, p t m * (κ * μ.d m (p t m))
        ≤ μ.T * (κ * μ.Rm m μ.zstar) + μ.zstar * ∫ t in (0 : ℝ)..μ.T, κ * μ.d m (p t m) := by
      intro m
      have hmeas : Measurable (fun t => p t m) := (measurable_pi_apply m).comp hpm
      have e1 : ∫ t in (0 : ℝ)..μ.T, p t m * (κ * μ.d m (p t m))
          = ∫ t in (0 : ℝ)..μ.T, clamp μ (p t m) * (κ * μ.d m (clamp μ (p t m))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT.le] at ht
        simp only [clamp_eq μ (hpI t ht m)]
      have e2 : ∫ t in (0 : ℝ)..μ.T, κ * μ.d m (p t m)
          = ∫ t in (0 : ℝ)..μ.T, κ * μ.d m (clamp μ (p t m)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT.le] at ht
        simp only [clamp_eq μ (hpI t ht m)]
      rw [e1, e2]
      have mD : Measurable (fun t => μ.d m (clamp μ (p t m))) :=
        (dc_cont μ m).measurable.comp hmeas
      have mC : Measurable (fun t => clamp μ (p t m)) := (clamp_cont μ).measurable.comp hmeas
      have iD : IntervalIntegrable (fun t => κ * μ.d m (clamp μ (p t m))) volume 0 μ.T :=
        ii_of_bound μ (mD.const_mul κ) 0 (κ * μ.M₁) (fun t =>
          ⟨mul_nonneg hκ (μ.d_nonneg _ _), mul_le_mul_of_nonneg_left (μ.d_le _ _) hκ⟩)
      have iA : IntervalIntegrable (fun t => clamp μ (p t m) * (κ * μ.d m (clamp μ (p t m))))
          volume 0 μ.T :=
        ii_of_bound μ (mC.mul (mD.const_mul κ)) 0 (μ.pinf * (κ * μ.M₁)) (fun t =>
          ⟨mul_nonneg (clamp_mem μ _).1 (mul_nonneg hκ (μ.d_nonneg _ _)),
           mul_le_mul (clamp_mem μ _).2 (mul_le_mul_of_nonneg_left (μ.d_le _ _) hκ)
            (mul_nonneg hκ (μ.d_nonneg _ _)) μ.pinf_pos.le⟩)
      have iB : IntervalIntegrable
          (fun t => κ * μ.Rm m μ.zstar + μ.zstar * (κ * μ.d m (clamp μ (p t m)))) volume 0 μ.T :=
        intervalIntegrable_const.add (iD.const_mul μ.zstar)
      calc ∫ t in (0 : ℝ)..μ.T, clamp μ (p t m) * (κ * μ.d m (clamp μ (p t m)))
          ≤ ∫ t in (0 : ℝ)..μ.T, (κ * μ.Rm m μ.zstar
              + μ.zstar * (κ * μ.d m (clamp μ (p t m)))) := by
            apply intervalIntegral.integral_mono_on hT.le iA iB
            intro t _
            have hx := clamp_mem μ (p t m)
            have hR := Rm_ge μ m μ.zstar _ hx
            set x := clamp μ (p t m)
            have : x * (κ * μ.d m x) = κ * (μ.d m x * (x - μ.zstar)) + μ.zstar * (κ * μ.d m x) := by
              ring
            rw [this]
            have := mul_le_mul_of_nonneg_left hR hκ
            linarith
        _ = μ.T * (κ * μ.Rm m μ.zstar)
              + μ.zstar * ∫ t in (0 : ℝ)..μ.T, κ * μ.d m (clamp μ (p t m)) := by
            rw [intervalIntegral.integral_add intervalIntegrable_const (iD.const_mul μ.zstar),
              intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
            simp
    calc ∑ m, ∫ t in (0 : ℝ)..μ.T, p t m * (κ * μ.d m (p t m))
        ≤ ∑ m, (μ.T * (κ * μ.Rm m μ.zstar)
            + μ.zstar * ∫ t in (0 : ℝ)..μ.T, κ * μ.d m (p t m)) :=
          Finset.sum_le_sum (fun m _ => hA m)
      _ = κ * (μ.T * ∑ m, μ.Rm m μ.zstar)
            + μ.zstar * ∑ m, ∫ t in (0 : ℝ)..μ.T, κ * μ.d m (p t m) := by
          have a1 : ∑ m, μ.T * (κ * μ.Rm m μ.zstar) = κ * (μ.T * ∑ m, μ.Rm m μ.zstar) := by
            rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
          rw [Finset.sum_add_distrib, a1, ← Finset.mul_sum]
      _ ≤ κ * (μ.T * ∑ m, μ.Rm m μ.zstar) + μ.zstar * (κ * μ.c) := by
          have := mul_le_mul_of_nonneg_left hpc hz0
          linarith
      _ = κ * (μ.T * ∑ m, μ.pstar m * μ.d m (μ.pstar m)) := by
          simp only [Rm_eq μ, Model.pstar]
          have hs : μ.zstar * μ.c = μ.zstar * (μ.T * ∑ m, μ.d m (μ.P m μ.zstar)) := by
            linarith
          have : ∑ m, μ.d m (μ.P m μ.zstar) * (μ.P m μ.zstar - μ.zstar)
              = ∑ m, μ.P m μ.zstar * μ.d m (μ.P m μ.zstar)
                - μ.zstar * ∑ m, μ.d m (μ.P m μ.zstar) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro m _; ring
          rw [this]
          have e : μ.zstar * (κ * μ.c) = κ * (μ.zstar * μ.c) := by ring
          rw [e, hs]; ring

end PDP14

open PDP14 in
theorem solution {M : ℕ} (μ : Model M) :
    FluidFeasible μ.d μ.pinf μ.c μ.T (fun _ m => μ.pstar m) ∧
    fluidValue μ.d μ.pinf μ.c μ.T = μ.T * ∑ m, μ.pstar m * μ.d m (μ.pstar m) ∧
    μ.zstar * (μ.c - μ.T * ∑ m, μ.d m (μ.P m μ.zstar)) = 0 ∧
    ∀ n : ℕ, fluidValueN μ.d μ.pinf μ.c μ.T n
      = (n : ℝ) * (μ.T * ∑ m, μ.pstar m * μ.d m (μ.pstar m)) := by
  obtain ⟨hfeas, hslack⟩ := kkt μ
  refine ⟨⟨measurable_const, fun t _ m => μ.P_mem m _, ?_⟩, ?_, hslack, ?_⟩
  · simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [← Finset.mul_sum]; exact hfeas
  · have h := fluid_scaled μ 1 zero_le_one
    simp only [one_mul] at h
    exact h
  · intro n
    exact fluid_scaled μ n (Nat.cast_nonneg n)
