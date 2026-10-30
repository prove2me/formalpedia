-- Prove2me | solution 1 for SLPEPricing.Regret.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:35:00.673858+00:00
-- url     : https://prove2.me/submissions/9b5be11e-3f06-4b9b-b6a0-854bb8bd99c7

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open SLPEPricing.Regret

namespace SLPEL3

lemma delta_pow (μ : ℝ) (k : ℕ) : μ * Delta μ (k + 1) = (μ / 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp [Delta]; ring
  | succ k ih =>
    have : Delta μ (k + 2) = μ * Delta μ (k + 1) ^ 2 := rfl
    rw [show k + 1 + 1 = k + 2 by ring, this, pow_succ 2 k, pow_mul, ← ih]
    ring

lemma abs_le_of_deriv {F G F' G' : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hF : ∀ u ∈ Set.Icc 0 h, HasDerivAt F (F' u) u) (hG : ∀ u ∈ Set.Icc 0 h, HasDerivAt G (G' u) u)
    (hb : ∀ u ∈ Set.Icc 0 h, |F' u| ≤ G' u) (h0 : F 0 = 0) (hG0 : G 0 = 0) : |F h| ≤ G h := by
  have hm1 : MonotoneOn (fun u => G u - F u) (Set.Icc 0 h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h)
    · intro u hu; exact ((hG u hu).sub (hF u hu)).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact ((hG u (Set.Ioo_subset_Icc_self hu)).sub
        (hF u (Set.Ioo_subset_Icc_self hu))).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu' := Set.Ioo_subset_Icc_self hu
      rw [show deriv (fun u => G u - F u) u = G' u - F' u from ((hG u hu').sub (hF u hu')).deriv]
      have := hb u hu'
      linarith [le_abs_self (F' u)]
  have hm2 : MonotoneOn (fun u => G u + F u) (Set.Icc 0 h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h)
    · intro u hu; exact ((hG u hu).add (hF u hu)).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact ((hG u (Set.Ioo_subset_Icc_self hu)).add
        (hF u (Set.Ioo_subset_Icc_self hu))).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu' := Set.Ioo_subset_Icc_self hu
      rw [show deriv (fun u => G u + F u) u = G' u + F' u from ((hG u hu').add (hF u hu')).deriv]
      have := hb u hu'
      linarith [neg_abs_le (F' u)]
  have h1 := hm1 (Set.left_mem_Icc.mpr hh) (Set.right_mem_Icc.mpr hh) hh
  have h2 := hm2 (Set.left_mem_Icc.mpr hh) (Set.right_mem_Icc.mpr hh) hh
  simp only [h0, hG0, sub_zero, add_zero] at h1 h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- symmetric difference quotient error with the sharp constant -/
lemma central_diff (d : ℝ → ℝ) (K₁ : ℝ) (hd : ContDiff ℝ 3 d)
    (hK₁ : ∀ k ≤ 3, ∀ p ∈ Set.Icc (-1 : ℝ) 2, |iteratedDeriv k d p| ≤ K₁)
    (m h : ℝ) (hh : 0 ≤ h) (hdom : Set.Icc (m - h) (m + h) ⊆ Set.Icc (-1) 2) :
    |d (m + h) - d (m - h) - 2 * h * deriv d m| ≤ K₁ * h ^ 3 / 3 := by
  have hd1 : Differentiable ℝ d := hd.differentiable (by norm_num)
  have h2 : ContDiff ℝ 2 (deriv d) := by
    have h3 : ContDiff ℝ (2 + 1) d := by convert hd using 1; rfl
    rw [contDiff_succ_iff_deriv] at h3
    exact h3.2.2
  have hdd : Differentiable ℝ (deriv d) := h2.differentiable (by norm_num)
  have h1' : ContDiff ℝ 1 (deriv (deriv d)) := by
    have h3 : ContDiff ℝ (1 + 1) (deriv d) := by convert h2 using 1; rfl
    rw [contDiff_succ_iff_deriv] at h3
    exact h3.2.2
  have hddd : Differentiable ℝ (deriv (deriv d)) := h1'.differentiable (by norm_num)
  have hb3 : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |deriv (deriv (deriv d)) x| ≤ K₁ := fun x hx => by
    have := hK₁ 3 le_rfl x hx
    simpa [iteratedDeriv_succ] using this
  have hin : ∀ u ∈ Set.Icc 0 h, m + u ∈ Set.Icc (-1 : ℝ) 2 ∧ m - u ∈ Set.Icc (-1 : ℝ) 2 := by
    intro u hu
    exact ⟨hdom ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩,
      hdom ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩⟩
  -- derivatives of `u ↦ g (m + u)` and `u ↦ g (m - u)`
  have dplus : ∀ (g : ℝ → ℝ), Differentiable ℝ g → ∀ u,
      HasDerivAt (fun u => g (m + u)) (deriv g (m + u)) u := by
    intro g hg u
    have := (hg (m + u)).hasDerivAt.comp u ((hasDerivAt_id' u).const_add m)
    simpa [Function.comp_def] using this
  have dminus : ∀ (g : ℝ → ℝ), Differentiable ℝ g → ∀ u,
      HasDerivAt (fun u => g (m - u)) (-deriv g (m - u)) u := by
    intro g hg u
    have := (hg (m - u)).hasDerivAt.comp u ((hasDerivAt_id' u).const_sub m)
    simpa [Function.comp_def] using this
  -- level 1
  have L1 : ∀ u ∈ Set.Icc 0 h,
      |deriv (deriv d) (m + u) - deriv (deriv d) (m - u)| ≤ 2 * K₁ * u := by
    intro u hu
    have hsub : Set.Icc 0 u ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl hu.2
    have := abs_le_of_deriv (F := fun v => deriv (deriv d) (m + v) - deriv (deriv d) (m - v))
      (G := fun v => 2 * K₁ * v)
      (F' := fun v => deriv (deriv (deriv d)) (m + v) + deriv (deriv (deriv d)) (m - v))
      (G' := fun _ => 2 * K₁) hu.1
      (fun v _ => by
        have := (dplus _ hddd v).sub (dminus _ hddd v)
        rw [sub_neg_eq_add] at this; exact this)
      (fun v _ => by simpa using ((hasDerivAt_id v).const_mul (2 * K₁)))
      (fun v hv => by
        obtain ⟨a1, a2⟩ := hin v (hsub hv)
        have := abs_add_le (deriv (deriv (deriv d)) (m + v)) (deriv (deriv (deriv d)) (m - v))
        linarith [hb3 _ a1, hb3 _ a2])
      (by simp) (by simp)
    simpa using this
  -- level 2
  have L2 : ∀ u ∈ Set.Icc 0 h,
      |deriv d (m + u) + deriv d (m - u) - 2 * deriv d m| ≤ K₁ * u ^ 2 := by
    intro u hu
    have hsub : Set.Icc 0 u ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl hu.2
    have := abs_le_of_deriv (F := fun v => deriv d (m + v) + deriv d (m - v) - 2 * deriv d m)
      (G := fun v => K₁ * v ^ 2)
      (F' := fun v => deriv (deriv d) (m + v) - deriv (deriv d) (m - v))
      (G' := fun v => 2 * K₁ * v) hu.1
      (fun v _ => by
        have := ((dplus _ hdd v).add (dminus _ hdd v)).sub_const (2 * deriv d m)
        rw [← sub_eq_add_neg] at this; exact this)
      (fun v _ => by
        have := (hasDerivAt_pow 2 v).const_mul K₁
        exact this.congr_deriv (by push_cast; ring))
      (fun v hv => L1 v (hsub hv))
      (by simp only [add_zero, sub_zero]; ring_nf) (by simp)
    simpa using this
  -- level 3
  have := abs_le_of_deriv (F := fun v => d (m + v) - d (m - v) - 2 * v * deriv d m)
      (G := fun v => K₁ * v ^ 3 / 3)
      (F' := fun v => deriv d (m + v) + deriv d (m - v) - 2 * deriv d m)
      (G' := fun v => K₁ * v ^ 2) hh
      (fun v _ => by
        have := ((dplus _ hd1 v).sub (dminus _ hd1 v)).sub
          ((hasDerivAt_id' v).const_mul 2 |>.mul_const (deriv d m))
        exact this.congr_deriv (by ring))
      (fun v _ => by
        have := ((hasDerivAt_pow 3 v).const_mul K₁).div_const 3
        exact this.congr_deriv (by push_cast; ring))
      (fun v hv => L2 v hv)
      (by simp) (by simp)
  simpa using this

end SLPEL3

open SLPEL3

theorem solution (d : ℝ → ℝ) (K₁ μ ρ : ℝ) (hd : ContDiff ℝ 3 d)
    (hK₁ : ∀ k ≤ 3, ∀ p ∈ Set.Icc (-1 : ℝ) 2, |iteratedDeriv k d p| ≤ K₁)
    (hμ : 0 < μ) (hρ : 0 < ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ)
    (T : ℕ) (hT : 2 ≤ T) (i : ℕ) (hi : 1 ≤ i)
    (hA2 : Assumption2At μ ρ T sel ε i)
    (hdom : Set.Icc (pL d μ ρ amax sel ε T i) (pH d μ ρ amax sel ε T i) ⊆ Set.Icc (-1) 2) :
    |(roundObs d μ ρ amax sel ε T i (sel i).2.1 - roundObs d μ ρ amax sel ε T i (sel i).1) /
        (pM d μ ρ amax sel ε T i - pL d μ ρ amax sel ε T i) -
        deriv d ((pM d μ ρ amax sel ε T i + pL d μ ρ amax sel ε T i) / 2)| ≤
      1 / 2 * K₁ * (Delta μ i ^ 2 / 12) ∧
    |(roundObs d μ ρ amax sel ε T i (sel i).2.2.2 - roundObs d μ ρ amax sel ε T i (sel i).2.2.1) /
        Delta μ i -
        deriv d ((pM d μ ρ amax sel ε T i + pH d μ ρ amax sel ε T i) / 2)| ≤
      1 / 2 * K₁ * (Delta μ i ^ 2 / 12) := by
  have hΔ : 0 < Delta μ i := by
    rcases i with _ | k
    · omega
    · have h := SLPEL3.delta_pow μ k
      have : Delta μ (k + 1) = (μ / 2) ^ (2 ^ k) / μ := by
        rw [eq_div_iff hμ.ne', mul_comm]; exact h
      rw [this]; positivity
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨b1', b2'⟩, ⟨c1, c2⟩, e1, e2⟩ := hA2
  set q := centre d μ ρ amax sel ε T i with hq
  set Δ := Delta μ i with hΔdef
  have hobs : ∀ t, roundObs d μ ρ amax sel ε T i t =
      d (blockPrice q Δ (roundStart μ ρ T i) (nRound μ ρ T i) t) + ε t := fun t => rfl
  have hpL : pL d μ ρ amax sel ε T i = q - Δ := rfl
  have hpM : pM d μ ρ amax sel ε T i = q := rfl
  have hpH : pH d μ ρ amax sel ε T i = q + Δ := rfl
  have bL : blockPrice q Δ (roundStart μ ρ T i) (nRound μ ρ T i) (sel i).1 = q - Δ := by
    unfold blockPrice; rw [if_pos a2]
  have bM : blockPrice q Δ (roundStart μ ρ T i) (nRound μ ρ T i) (sel i).2.1 = q := by
    unfold blockPrice; rw [if_neg (by omega), if_pos b2]
  have bM' : blockPrice q Δ (roundStart μ ρ T i) (nRound μ ρ T i) (sel i).2.2.1 = q := by
    unfold blockPrice; rw [if_neg (by omega), if_pos b2']
  have bH : blockPrice q Δ (roundStart μ ρ T i) (nRound μ ρ T i) (sel i).2.2.2 = q + Δ := by
    unfold blockPrice; rw [if_neg (by omega), if_neg (by omega)]
  rw [hobs, hobs, hobs, hobs, bL, bM, bM', bH, hpL, hpM, hpH, e1, e2]
  rw [hpL, hpH] at hdom
  have hK : K₁ * (Δ / 2) ^ 3 / 3 / Δ = 1 / 2 * K₁ * (Δ ^ 2 / 12) := by
    have hne : Δ ≠ 0 := hΔ.ne'
    field_simp; ring
  constructor
  · have hc := central_diff d K₁ hd hK₁ (q - Δ / 2) (Δ / 2) (by positivity)
      (fun x hx => hdom ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have e3 : q - Δ / 2 + Δ / 2 = q := by ring
    have e4 : q - Δ / 2 - Δ / 2 = q - Δ := by ring
    rw [e3, e4] at hc
    have e5 : (d q + ε (sel i).2.1 - (d (q - Δ) + ε (sel i).2.1)) / (q - (q - Δ)) -
        deriv d ((q + (q - Δ)) / 2) = (d q - d (q - Δ) - 2 * (Δ / 2) * deriv d (q - Δ / 2)) / Δ := by
      have : (q + (q - Δ)) / 2 = q - Δ / 2 := by ring
      rw [this, show q - (q - Δ) = Δ by ring]
      have hne : Δ ≠ 0 := hΔ.ne'
      field_simp; ring
    rw [e5, abs_div, abs_of_pos hΔ, ← hK]
    exact div_le_div_of_nonneg_right hc hΔ.le
  · have hc := central_diff d K₁ hd hK₁ (q + Δ / 2) (Δ / 2) (by positivity)
      (fun x hx => hdom ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have e3 : q + Δ / 2 + Δ / 2 = q + Δ := by ring
    have e4 : q + Δ / 2 - Δ / 2 = q := by ring
    rw [e3, e4] at hc
    have e5 : (d (q + Δ) + ε (sel i).2.2.2 - (d q + ε (sel i).2.2.2)) / Δ -
        deriv d ((q + (q + Δ)) / 2) = (d (q + Δ) - d q - 2 * (Δ / 2) * deriv d (q + Δ / 2)) / Δ := by
      have : (q + (q + Δ)) / 2 = q + Δ / 2 := by ring
      have hne : Δ ≠ 0 := hΔ.ne'
      rw [this]; field_simp; ring
    rw [e5, abs_div, abs_of_pos hΔ, ← hK]
    exact div_le_div_of_nonneg_right hc hΔ.le
