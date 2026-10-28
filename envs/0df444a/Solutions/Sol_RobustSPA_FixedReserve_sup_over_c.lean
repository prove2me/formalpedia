-- Prove2me | solution 1 for RobustSPA.FixedReserve.sup_over_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:40:46.428923+00:00
-- url     : https://prove2.me/submissions/b0fc7c6e-28d2-4433-b460-83aa6f3aff07

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

theorem supc_aux (k : ℕ) (N r : ℝ) (hN : N = (k : ℝ) + 2) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    let g : ℝ → ℝ := fun c => r * c ^ (k + 2) + (1 - r) * (N * c ^ (k + 1) - N * c ^ (k + 2))
    let cstar : ℝ := (1 - r) * (N - 1) / ((1 - r) * N - r)
    (r ≤ 1 / 2 →
      cstar ∈ Set.Icc ((N - 1) / N) 1 ∧
      g cstar = (1 - r) ^ (k + 2) * (N - 1) ^ (k + 1) / ((1 - r) * N - r) ^ (k + 1) ∧
      IsGreatest (g '' Set.Icc ((N - 1) / N) 1)
        ((1 - r) ^ (k + 2) * (N - 1) ^ (k + 1) / ((1 - r) * N - r) ^ (k + 1))) ∧
    (1 / 2 ≤ r → g 1 = r ∧ IsGreatest (g '' Set.Icc ((N - 1) / N) 1) r) := by
  intro g cstar
  obtain ⟨hr0, hr1⟩ := hr
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hNpos : 0 < N := by linarith
  -- derivative
  set B : ℝ → ℝ := fun c => (1 - r) * (N - 1) - ((1 - r) * N - r) * c with hB
  have hderiv : ∀ c, HasDerivAt g (N * c ^ k * B c) c := by
    intro c
    have h1 := (hasDerivAt_pow (k + 2) c)
    have h2 := (hasDerivAt_pow (k + 1) c)
    have := ((h1.const_mul r).add (((h2.const_mul N).sub (h1.const_mul N)).const_mul (1 - r)))
    refine this.congr_deriv ?_
    rw [show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
    simp only [hB]
    push_cast
    rw [hN]
    ring
  have hgc : Continuous g := by
    simp only [g]; fun_prop
  have hm0 : 0 ≤ (N - 1) / N := div_nonneg (by linarith) hNpos.le
  have hm1 : (N - 1) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  -- monotone on a set where B ≥ 0
  have mono : ∀ a b : ℝ, 0 ≤ a → (∀ c ∈ Set.Icc a b, 0 ≤ B c) → MonotoneOn g (Set.Icc a b) := by
    intro a b ha hBc
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hgc.continuousOn
      (fun x _ => (hderiv x).hasDerivWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := le_trans ha hx.1.le
    exact mul_nonneg (mul_nonneg hNpos.le (pow_nonneg hx0 _)) (hBc x ⟨hx.1.le, hx.2.le⟩)
  have anti : ∀ a b : ℝ, 0 ≤ a → (∀ c ∈ Set.Icc a b, B c ≤ 0) → AntitoneOn g (Set.Icc a b) := by
    intro a b ha hBc
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hgc.continuousOn
      (fun x _ => (hderiv x).hasDerivWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := le_trans ha hx.1.le
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hNpos.le (pow_nonneg hx0 _))
      (hBc x ⟨hx.1.le, hx.2.le⟩)
  have hg1 : g 1 = r := by simp only [g]; ring
  refine ⟨fun hrh => ?_, fun hrh => ⟨hg1, ?_⟩⟩
  · have hD : 0 < (1 - r) * N - r := by nlinarith
    have hcs_lo : (N - 1) / N ≤ cstar := by
      simp only [cstar]
      rw [div_le_div_iff₀ hNpos hD]; nlinarith
    have hcs_hi : cstar ≤ 1 := by
      simp only [cstar]
      rw [div_le_one hD]; nlinarith
    have hval : g cstar = (1 - r) ^ (k + 2) * (N - 1) ^ (k + 1) / ((1 - r) * N - r) ^ (k + 1) := by
      have hc : cstar * ((1 - r) * N - r) = (1 - r) * (N - 1) := by
        simp only [cstar]; field_simp
      have : g cstar = cstar ^ (k + 1) * (1 - r) := by
        simp only [g]
        have e : r * cstar ^ (k + 2) + (1 - r) * (N * cstar ^ (k + 1) - N * cstar ^ (k + 2)) =
            cstar ^ (k + 1) * ((1 - r) * N - cstar * ((1 - r) * N - r)) := by ring
        rw [e, hc]; ring
      rw [this]
      simp only [cstar]
      rw [div_pow, mul_pow]
      field_simp
      ring
    refine ⟨⟨hcs_lo, hcs_hi⟩, hval, ⟨cstar, ⟨hcs_lo, hcs_hi⟩, hval⟩, ?_⟩
    rintro y ⟨c, hc, rfl⟩
    rw [← hval]
    have hc0 : 0 ≤ c := le_trans hm0 hc.1
    rcases le_total c cstar with hcc | hcc
    · apply mono ((N - 1) / N) cstar hm0 _ ⟨hc.1, hcc⟩ ⟨hcs_lo, le_rfl⟩ hcc
      intro x hx
      simp only [hB]
      have : x * ((1 - r) * N - r) ≤ (1 - r) * (N - 1) := by
        have := mul_le_mul_of_nonneg_right hx.2 hD.le
        simp only [cstar] at this
        rwa [div_mul_cancel₀ _ hD.ne'] at this
      linarith
    · apply anti cstar 1 (le_trans hm0 hcs_lo) _ ⟨le_rfl, hcs_hi⟩ ⟨hcc, hc.2⟩ hcc
      intro x hx
      simp only [hB]
      have : (1 - r) * (N - 1) ≤ x * ((1 - r) * N - r) := by
        have := mul_le_mul_of_nonneg_right hx.1 hD.le
        simp only [cstar] at this
        rwa [div_mul_cancel₀ _ hD.ne'] at this
      linarith
  · refine ⟨⟨1, ⟨hm1, le_rfl⟩, hg1⟩, ?_⟩
    rintro y ⟨c, hc, rfl⟩
    rw [← hg1]
    apply mono ((N - 1) / N) 1 hm0 _ hc ⟨hm1, le_rfl⟩ hc.2
    intro x hx
    simp only [hB]
    have hx0 : 0 ≤ x := le_trans hm0 hx.1
    rcases le_total ((1 - r) * N - r) 0 with hD | hD
    · nlinarith
    · have := mul_le_mul_of_nonneg_left hx.2 hD
      nlinarith


theorem solution (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    let g : ℝ → ℝ := fun c => r * c ^ n + (1 - r) * ((n : ℝ) * c ^ (n - 1) - (n : ℝ) * c ^ n)
    let cstar : ℝ := (1 - r) * ((n : ℝ) - 1) / ((1 - r) * n - r)
    (r ≤ 1 / 2 →
      cstar ∈ Set.Icc (((n : ℝ) - 1) / n) 1 ∧
      g cstar = (1 - r) ^ n * ((n : ℝ) - 1) ^ (n - 1) / ((1 - r) * n - r) ^ (n - 1) ∧
      IsGreatest (g '' Set.Icc (((n : ℝ) - 1) / n) 1)
        ((1 - r) ^ n * ((n : ℝ) - 1) ^ (n - 1) / ((1 - r) * n - r) ^ (n - 1))) ∧
    (1 / 2 ≤ r → g 1 = r ∧ IsGreatest (g '' Set.Icc (((n : ℝ) - 1) / n) 1) r) := by
  intro g cstar
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk1 : k + 2 - 1 = k + 1 := by omega
  rw [hk1]
  exact supc_aux k _ r (by push_cast; ring) hr
