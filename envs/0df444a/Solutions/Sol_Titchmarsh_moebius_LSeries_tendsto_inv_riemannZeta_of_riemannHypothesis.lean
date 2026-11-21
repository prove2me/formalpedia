-- Prove2me | solution 1 for Titchmarsh.moebius_LSeries_tendsto_inv_riemannZeta_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:48:16.408077+00:00
-- url     : https://prove2.me/submissions/55c0f5e1-bc53-4893-881c-8480860834b1

import Theorems.Thm_TauCeti_LSeries_differentiableOn_mul_integral_of_isBigO
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Finset Asymptotics

namespace MoebiusRH

/-- The Möbius function as a complex sequence. -/
noncomputable def μC (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)

lemma μC_zero : μC 0 = 0 := by simp [μC]

lemma norm_μC_le (n : ℕ) : ‖μC n‖ ≤ 1 := by
  unfold μC
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-! ### 3. The reciprocal of `ζ`, with its removable singularity at `1` filled in -/

/-- `1/ζ`, set to `0` at the pole `s = 1`. -/
noncomputable def Z (s : ℂ) : ℂ := if s = 1 then 0 else (riemannZeta s)⁻¹

lemma LSeries_μC_eq_Z {s : ℂ} (hs : 1 < s.re) : LSeries μC s = Z s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  unfold Z
  rw [if_neg hs1]
  exact (eq_inv_of_mul_eq_one_right h)

lemma Z_tendsto_one : Tendsto Z (𝓝[≠] 1) (𝓝 0) := by
  have h := riemannZeta_residue_one
  have h2 : Tendsto (fun s : ℂ => (s - 1) * ((s - 1) * riemannZeta s)⁻¹) (𝓝[≠] 1)
      (𝓝 (0 * (1 : ℂ)⁻¹)) := by
    refine Tendsto.mul ?_ (h.inv₀ one_ne_zero)
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (1 : ℂ))).sub_const (1 : ℂ)
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  rw [zero_mul] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [Z, if_neg hs1]
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs', one_mul]

lemma Z_continuousAt_one : ContinuousAt Z 1 := by
  rw [continuousAt_iff_punctured_nhds]
  have : Z 1 = 0 := by simp [Z]
  rw [this]
  exact Z_tendsto_one

lemma Z_differentiableAt_of_ne_one
    (hnz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ Z s := by
  have hd : DifferentiableAt ℂ (fun z => (riemannZeta z)⁻¹) s :=
    (differentiableAt_riemannZeta hs1).inv (hnz s hs hs1)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
  simp [Z, if_neg (show z ≠ 1 from hz)]

lemma Z_differentiableOn (hnz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ Z {z : ℂ | 1 / 2 < z.re} := by
  have hU : {z : ℂ | 1 / 2 < z.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; norm_num)
  rw [← differentiableOn_compl_singleton_and_continuousAt_iff hU]
  refine ⟨fun z hz => ?_, Z_continuousAt_one⟩
  exact (Z_differentiableAt_of_ne_one hnz hz.1 hz.2).differentiableWithinAt

lemma Z_differentiableAt (hnz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ Z s :=
  (Z_differentiableOn hnz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)


/-- Under RH, `ζ` has no zeros with `Re s > 1/2`, `s ≠ 1`. -/
lemma zeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro h0
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s h0 htriv hs1
  linarith

/-- Abel summation: if the partial sums of `f` are `O(n^r)`, the partial sums of the Dirichlet
series converge, for `r < Re s`, to `s ∫₁^∞ A(t) t^{-s-1} dt` (adapted from Mathlib's
`LSeries_eq_mul_integral_aux`, without assuming absolute convergence). -/
lemma partial_tendsto {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ}
    (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, (k : ℂ) ^ (-s) * f k) atTop
      (𝓝 (s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1)))) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
  have h₄ : ∀ n, ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := fun n ↦ by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop), hf, zero_add, zero_add]
  simp_rw [← h₄] at hO
  rw [← integral_const_mul]
  convert!
    tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0) ?_ hf h₃ ?_
      ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne', h₄]
    · ring_nf
    · exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using! hr.trans_lt hs)).locallyIntegrableOn
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
    · exact isBigO_norm_left.mp <| (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  · refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · simpa [-neg_add_rev, neg_add'] using! isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)

end MoebiusRH

open MoebiusRH in
theorem solution (hRH : RiemannHypothesis) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s))
        atTop (𝓝 (riemannZeta s)⁻¹) := by
  intro s hs hs1
  -- Littlewood: `M(n) = O(n^r)` for every `r > 1/2`
  have hO : ∀ r : ℝ, 1 / 2 < r → (fun n ↦ ∑ k ∈ Icc 1 n, μC k) =O[atTop] fun n ↦ (n : ℝ) ^ r := by
    intro r hr
    have h := moebius_summatory_rpow_bound_of_riemannHypothesis hRH (r - 1 / 2) (by linarith)
    simpa [μC, show 1 / 2 + (r - 1 / 2) = r by ring] using h
  set G : ℂ → ℂ := fun s ↦ s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, μC k) * t ^ (-(s + 1))
    with hG
  -- `G` is holomorphic on `Re s > 1/2`
  have hGd : DifferentiableOn ℂ G {z : ℂ | 1 / 2 < z.re} := by
    intro z hz
    have hz' : (1 : ℝ) / 2 < z.re := hz
    set r := (1 / 2 + z.re) / 2
    have hd := TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO μC (hO r (by
      simp only [r]; linarith))
    have hopen : IsOpen {w : ℂ | r < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hzr : z ∈ {w : ℂ | r < w.re} := by simp only [Set.mem_setOf_eq, r]; linarith
    exact (hd.differentiableAt (hopen.mem_nhds hzr)).differentiableWithinAt
  have hnz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := fun s h h1 =>
    zeta_ne_zero_of_RH hRH h h1
  have hZd := Z_differentiableOn hnz
  -- `G = Z` on `Re s > 1`
  have hU : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGZ1 : ∀ z : ℂ, 1 < z.re → G z = Z z := by
    intro z hz
    rw [← LSeries_μC_eq_Z hz]
    have hsum : LSeriesSummable μC z :=
      ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hz
    have := LSeries_eq_mul_integral μC (r := 3 / 4) (by norm_num) (by linarith) hsum
      (hO (3 / 4) (by norm_num))
    rw [this]
  have hEq : EqOn G Z {z : ℂ | 1 / 2 < z.re} := by
    refine (hGd.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hZd.analyticOnNhd hU)
      (convex_halfSpace_re_gt (1 / 2)).isPreconnected (z₀ := 2) (by simp; norm_num) ?_
    have h2 : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [h2] with z hz
    exact hGZ1 z hz
  -- partial sums converge to `G s`
  have hr : (0 : ℝ) ≤ (1 / 2 + s.re) / 2 := by linarith
  have hlim := partial_tendsto (f := μC) μC_zero hr (s := s) (by linarith)
    (hO _ (by linarith))
  have hval : G s = (riemannZeta s)⁻¹ := by
    rw [hEq hs]; simp [Z, hs1]
  rw [← hval]
  refine hlim.congr fun N => ?_
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), μC_zero, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun n _ => by simp [μC, mul_comm]
