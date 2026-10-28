-- Prove2me | solution 1 for SliceRibbon.radialSq_not_isLocalMax_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:57:27.996172+00:00
-- url     : https://prove2.me/submissions/fcbe2b01-ee62-4f1b-b7f5-6d3b532a08c0

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric
open scoped ContDiff

namespace SR479

open SliceRibbon Filter Topology

lemma oneD (g g' : ℝ → ℝ) (c : ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : HasDerivAt g' c 0) (hmax : IsLocalMax g 0) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  set h : ℝ → ℝ := fun t => g t - (c / 4) * t ^ 2 with hh
  have hd : ∀ t, HasDerivAt h (g' t - (c / 2) * t) t := by
    intro t
    have := ((hg t).sub ((hasDerivAt_pow 2 t).const_mul (c / 4)) :
      HasDerivAt (fun x => g x - c / 4 * x ^ 2) _ t)
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring
  have hderiv : deriv h = fun t => g' t - (c / 2) * t := funext fun t => (hd t).deriv
  have hd2 : HasDerivAt (fun t => g' t - (c / 2) * t) (c - c / 2) 0 := by
    have := (hg'.sub ((hasDerivAt_id (0:ℝ)).const_mul (c / 2)) :
      HasDerivAt (fun x => g' x - c / 2 * id x) _ 0)
    exact this.congr_deriv (by ring)
  have h1 : deriv (deriv h) 0 > 0 := by
    rw [hderiv, hd2.deriv]; linarith
  have h0 : deriv h 0 = 0 := by
    rw [hderiv]
    have := hmax.hasDerivAt_eq_zero (hg 0)
    simp [this]
  have hmin : IsLocalMin h 0 :=
    isLocalMin_of_deriv_deriv_pos h1 h0 (hd 0).continuousAt
  have hev := hmin.and hmax
  rcases Metric.eventually_nhds_iff.1 hev with ⟨δ, hδ, hball⟩
  have := hball (y := δ / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  obtain ⟨hA, hB⟩ := this
  simp only [hh] at hA
  have : 0 < (c / 4) * (δ / 2) ^ 2 := by positivity
  simp at hA
  linarith

/-- directional first and second order conditions -/
lemma dirCond (F : R2 → R4) (hF : ContDiff ℝ ∞ F) (z : R2)
    (hmax : IsLocalMax (radialSq F) z) (w : R2) :
    inner ℝ (F z) (fderiv ℝ F z w) = 0 ∧
    inner ℝ (fderiv ℝ F z w) (fderiv ℝ F z w) +
      inner ℝ (F z) (fderiv ℝ (fderiv ℝ F) z w w) ≤ 0 := by
  have hF2 : ContDiff ℝ 2 F := contDiff_infty.1 hF 2
  have hD : Differentiable ℝ F := hF2.differentiable (by norm_num)
  have hD2 : Differentiable ℝ (fderiv ℝ F) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • w) w t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  have hFl : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (z + s • w)) (fderiv ℝ F (z + t • w) w) t :=
    fun t => (hD _).hasFDerivAt.comp_hasDerivAt t (hline t)
  let g : ℝ → ℝ := fun t => ‖F (z + t • w)‖ ^ 2
  let g' : ℝ → ℝ := fun t => 2 * inner ℝ (F (z + t • w)) (fderiv ℝ F (z + t • w) w)
  have hg : ∀ t, HasDerivAt g (g' t) t := fun t => (hFl t).norm_sq
  have hDl : HasDerivAt (fun s : ℝ => fderiv ℝ F (z + s • w) w)
      (fderiv ℝ (fderiv ℝ F) z w w) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ F (z + s • w))
        (fderiv ℝ (fderiv ℝ F) (z + (0:ℝ) • w) w) 0 :=
      (hD2 _).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hline 0)
    simp only [zero_smul, add_zero] at h1
    have := h1.clm_apply (hasDerivAt_const (0:ℝ) w)
    simpa using this
  have hF0 := hFl 0
  simp only [zero_smul, add_zero] at hF0
  have hg' : HasDerivAt g' (2 * (inner ℝ (fderiv ℝ F z w) (fderiv ℝ F z w) +
      inner ℝ (F z) (fderiv ℝ (fderiv ℝ F) z w w))) 0 := by
    have := (hF0.inner ℝ hDl).const_mul 2
    refine this.congr_deriv ?_
    simp only [zero_smul, add_zero]
    ring
  have hlm : IsLocalMax g 0 := by
    have ht : Tendsto (fun s : ℝ => z + s • w) (𝓝 0) (𝓝 z) := by
      have := (hline 0).continuousAt.tendsto
      simpa using this
    have := ht.eventually hmax
    filter_upwards [this] with t ht
    simpa [g, radialSq] using ht
  refine ⟨?_, ?_⟩
  · have := hlm.hasDerivAt_eq_zero (hg 0)
    simp [g'] at this
    exact this
  · have := oneD g g' _ hg hg' hlm
    linarith

end SR479

open SliceRibbon in
theorem solution (F : R2 → R4) (hF : ContDiff ℝ ∞ F)
    (himm : ∀ z : R2, ‖z‖ < 1 → Function.Injective (fderiv ℝ F z))
    (hmin : IsMinimalOnDisk F) (z : R2) (hz : ‖z‖ < 1) :
    ¬ IsLocalMax (radialSq F) z := by
  intro hmax
  set L := fderiv ℝ F z with hL
  set B := fderiv ℝ (fderiv ℝ F) z with hB
  set e0 : R2 := EuclideanSpace.single 0 1
  set e1 : R2 := EuclideanSpace.single 1 1
  have hsymm : B e0 e1 = B e1 e0 := by
    have := ((contDiff_infty.1 hF 2).contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
    exact (this e0 e1)
  have hsec : ∀ i j : Fin 2, secondPartial F z i j =
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro i j
    simp [secondPartial, iteratedFDeriv_two_apply, hB]
  obtain ⟨u, hu⟩ := hmin z hz
  have hfirst : ∀ w, inner ℝ (F z) (L w) = 0 := fun w => (SR479.dirCond F hF z hmax w).1
  have hsecond : ∀ a b : ℝ, inner ℝ (L (a • e0 + b • e1)) (L (a • e0 + b • e1)) +
      inner ℝ (F z) (B (a • e0 + b • e1) (a • e0 + b • e1)) ≤ 0 :=
    fun a b => (SR479.dirCond F hF z hmax _).2
  set g00 := inner ℝ (L e0) (L e0)
  set g01 := inner ℝ (L e0) (L e1)
  set g11 := inner ℝ (L e1) (L e1)
  set p00 := inner ℝ (F z) (B e0 e0)
  set p01 := inner ℝ (F z) (B e0 e1)
  set p11 := inner ℝ (F z) (B e1 e1)
  have hQ : ∀ a b : ℝ, a ^ 2 * (g00 + p00) + 2 * a * b * (g01 + p01) + b ^ 2 * (g11 + p11) ≤ 0 := by
    intro a b
    have := hsecond a b
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at this
    rw [← hsymm, real_inner_comm (L e0) (L e1)] at this
    refine le_trans (le_of_eq ?_) this
    simp only [g00, g01, g11, p00, p01, p11]
    ring
  have hcon : g11 * p00 - 2 * g01 * p01 + g00 * p11 = 0 := by
    have h := hfirst u
    change L u = _ at hu
    rw [hu] at h
    simp only [firstPartial, hsec] at h
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right] at h
    rw [← hL] at h
    linarith
  have hinj := himm z hz
  have hg11 : 0 < g11 := by
    have hne : L e1 ≠ 0 := by
      intro h
      have : e1 = 0 := hinj (by rw [h, map_zero])
      have h2 : (e1 : R2) 1 = 1 := by simp [e1]
      rw [this] at h2; simp at h2
    exact real_inner_self_pos.2 hne
  have hdet : 0 < g00 * g11 - g01 ^ 2 := by
    have hne : L (g11 • e0 - g01 • e1) ≠ 0 := by
      intro h
      have : g11 • e0 - g01 • e1 = 0 := hinj (by rw [h, map_zero])
      have h2 := congrArg (fun v : R2 => v 0) this
      simp [e0, e1] at h2
      linarith
    have hp := real_inner_self_pos.2 hne
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right] at hp
    rw [real_inner_comm (L e0) (L e1)] at hp
    have : 0 < g11 * (g00 * g11 - g01 ^ 2) := lt_of_lt_of_eq hp (by simp only [g00, g01, g11]; ring)
    exact pos_of_mul_pos_right this hg11.le
  have q1 := hQ 0 1
  have q2 := hQ g11 (-g01)
  have q1' : g11 + p11 ≤ 0 := by simpa using q1
  have key : g11 * (2 * (g00 * g11 - g01 ^ 2)) = (g11 ^ 2 * (g00 + p00) + 2 * g11 * (-g01) * (g01 + p01)
      + (-g01) ^ 2 * (g11 + p11)) + (g00 * g11 - g01 ^ 2) * (g11 + p11) := by
    linear_combination (-g11) * hcon
  have h3 := mul_nonpos_of_nonneg_of_nonpos hdet.le q1'
  have h4 := mul_pos hg11 hdet
  linarith
