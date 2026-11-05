-- Prove2me | solution 1 for PrimalDualPricing.Regret.proposition_1_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:54:50.111748+00:00
-- url     : https://prove2.me/submissions/af8f7efb-f046-4498-9ce4-02fd6180a84b

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Model

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
theorem solution {M : ℕ} (μ : Model M) (m : Fin M) :
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
