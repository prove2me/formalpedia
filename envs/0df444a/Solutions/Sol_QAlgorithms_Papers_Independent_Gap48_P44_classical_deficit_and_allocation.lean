-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.classical_deficit_and_allocation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:06:52.63031+00:00
-- url     : https://prove2.me/submissions/2011c3ae-bec4-4826-92f7-461ba1d17321

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P44
open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem g78b_two_log_le {y : ℝ} (hy : 1 ≤ y) : 2 * Real.log y ≤ y - 1 / y := by
  let ψ : ℝ → ℝ := fun t => t - t⁻¹ - 2 * Real.log t
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt ψ (1 - (-(x ^ 2)⁻¹) - 2 * x⁻¹) x := by
    intro x hx0
    have := ((hasDerivAt_id' x).sub (hasDerivAt_inv hx0.ne')).sub
      ((Real.hasDerivAt_log hx0.ne').const_mul 2)
    exact this
  have hmono : MonotoneOn ψ (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      have : (1:ℝ) ≤ x := hx
      exact (hd x (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have : (1:ℝ) < x := hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have : (1:ℝ) < x := hx
      rw [(hd x (by linarith)).deriv]
      have : 1 - (-(x ^ 2)⁻¹) - 2 * x⁻¹ = (1 - x⁻¹) ^ 2 := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp only [ψ, inv_one, Real.log_one] at this
  rw [one_div]
  linarith

theorem g78b_g_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := h1.mul (h1.log (by linarith))
  have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
  have := h2.sub h3
  refine this.congr_deriv ?_
  simp only [id, one_mul]
  field_simp
  ring

/-- u = log(x+1) - log x bounds -/
theorem g78b_u_bounds {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
    Real.log (x + 1) - Real.log x ≤ 1 / x ∧
    2 * (Real.log (x + 1) - Real.log x) ≤ 1 / x + 1 / (x + 1) := by
  have hy : 0 < (x + 1) / x := by positivity
  have e : Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) := by
    rw [Real.log_div (by linarith) hx.ne']
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · have := Real.one_sub_inv_le_log_of_pos hy
    have h2 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos hy
    have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  · have := g78b_two_log_le (y := (x + 1) / x) (by rw [le_div_iff₀ hx]; linarith)
    have h2 : (x + 1) / x - 1 / ((x + 1) / x) = 1 / x + 1 / (x + 1) := by field_simp; ring
    linarith

theorem g78b_g_eq {x : ℝ} (hx : 0 < x) :
    g x = Real.log x + (x + 1) * (Real.log (x + 1) - Real.log x) := by
  unfold g; ring

theorem g78b_hh_ge {x : ℝ} (hx : 0 < x) : 1 ≤ (x + 1) * (Real.log (x + 1) - Real.log x) := by
  have := (g78b_u_bounds hx).1
  have h : (x + 1) * (1 / (x + 1)) = 1 := by field_simp
  nlinarith

theorem g78b_hh_le {x : ℝ} (hx : 0 < x) :
    (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 1 + 1 / x := by
  have := (g78b_u_bounds hx).2.1
  have h : (x + 1) * (1 / x) = 1 + 1 / x := by field_simp
  nlinarith

theorem g78b_hh_le2 {x : ℝ} (hx : 0 < x) :
    (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 1 + 1 / (2 * x) := by
  have := (g78b_u_bounds hx).2.2
  have h : (x + 1) * (1 / x + 1 / (x + 1)) = 2 * (1 + 1 / (2 * x)) := by field_simp; ring
  nlinarith

theorem g78b_hh_anti : AntitoneOn (fun x : ℝ => (x + 1) * (Real.log (x + 1) - Real.log x))
    (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => (x + 1) * (Real.log (x + 1) - Real.log x))
      (1 * (Real.log (x + 1) - Real.log x) + (x + 1) * (1 / (x + 1) * 1 - 1 / x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h3 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx.ne'
    have h2 := (h1.log (by linarith)).sub h3
    have := h1.mul h2
    refine (this.congr_deriv ?_)
    simp [one_div]
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    have := (g78b_u_bounds hx').2.1
    have h : (x + 1) * (1 / (x + 1) * 1 - 1 / x) = - (1 / x) := by field_simp; ring
    rw [h]; linarith

theorem g78b_key {x l : ℝ} (hx : 0 < x) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    l * (Real.log (l * x + 1) - Real.log (l * x)) ≤ Real.log (x + 1) - Real.log x := by
  have hp : 0 < (l * x + 1) / (l * x) := by positivity
  have hg := Real.geom_mean_le_arith_mean2_weighted hl0.le (by linarith : (0:ℝ) ≤ 1 - l)
    hp.le zero_le_one (by ring)
  rw [Real.one_rpow, mul_one] at hg
  have hr : l * ((l * x + 1) / (l * x)) + (1 - l) * 1 = (x + 1) / x := by
    field_simp; ring
  rw [hr] at hg
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hp l) hg
  rw [Real.log_rpow hp, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hx.ne'] at hlog
  exact hlog

theorem g78b_phi_mono {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    MonotoneOn (fun x : ℝ => g x - g (c * x)) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => g x - g (c * x))
      ((Real.log (x + 1) - Real.log x) -
        (Real.log (c * x + 1) - Real.log (c * x)) * (c * 1)) x := by
    intro x hx
    exact (g78b_g_hasDeriv hx).sub ((g78b_g_hasDeriv (mul_pos hc0 hx)).comp x
      ((hasDerivAt_id x).const_mul c))
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx' : 0 < x := hx
    rw [(hd x hx').deriv]
    have := g78b_key hx' hc0 hc1
    nlinarith

theorem g78b_cdiff {c y B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hy : 0 < y) (hyB : y ≤ B) :
    0 ≤ (g B - g (c * B)) - (g y - g (c * y)) ∧
    (g B - g (c * B)) - (g y - g (c * y)) ≤ 1 / (2 * (c * y)) := by
  have hB : 0 < B := lt_of_lt_of_le hy hyB
  have M := g78b_phi_mono hc0 hc1 hy hB hyB
  simp only at M
  refine ⟨by linarith, ?_⟩
  have hcB : 0 < c * B := by positivity
  have hcy : 0 < c * y := by positivity
  have A := g78b_hh_anti hcB hB (by nlinarith)
  have B1 := g78b_hh_ge hy
  have B2 := g78b_hh_le2 hcy
  simp only at A
  rw [g78b_g_eq hB, g78b_g_eq hcB, g78b_g_eq hy, g78b_g_eq hcy]
  generalize (B + 1) * (Real.log (B + 1) - Real.log B) = H1 at *
  generalize (c * B + 1) * (Real.log (c * B + 1) - Real.log (c * B)) = H2 at *
  generalize (y + 1) * (Real.log (y + 1) - Real.log y) = H3 at *
  generalize (c * y + 1) * (Real.log (c * y + 1) - Real.log (c * y)) = H4 at *
  rw [Real.log_mul hc0.ne' hB.ne', Real.log_mul hc0.ne' hy.ne']
  linarith

/-- PDF pp.9-10, Proposition 6: the proof supplies the missing printed LHS.
The first bound is in nats; the allocation conclusion is in bits.
Printed: only 5/(6 lambda N_S (1-eta)); changed: attach the difference explicitly
computed at the beginning of the proof. Why: the bound otherwise has no subject.
Independent moderation of this source-domain interpretation remains pending. -/
theorem solution (eta share budget : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hshare : share ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : 0 ≤ budget) (hthreshold : 2 ≤ share * (1 - eta) * budget) :
    (g budget + g (eta * budget) - g ((1 - eta) * budget) -
      (g (share * budget) + g (eta * budget) - g ((1 - eta) * share * budget)) ≤
        5 / (6 * share * budget * (1 - eta))) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      let allocation := 5 / (6 * epsilon * budget * (1 - eta) * Real.log 2)
      allocation ∈ Set.Icc (0 : ℝ) 1 → 2 ≤ allocation * (1 - eta) * budget →
      |thermalEntropy budget + thermalEntropy (eta * budget) -
        thermalEntropy ((1 - eta) * budget) -
        (thermalEntropy (allocation * budget) + thermalEntropy (eta * budget) -
          thermalEntropy ((1 - eta) * allocation * budget))| ≤ epsilon) := by
  obtain ⟨hs0, hs1⟩ := hshare
  have h0 : 0 < 1 - eta := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy : 0 < share * budget := by
    by_contra hc; push_neg at hc; nlinarith
  have hyB : share * budget ≤ budget := by nlinarith
  refine ⟨?_, ?_⟩
  · obtain ⟨_, h2⟩ := g78b_cdiff h0 (by linarith) hy hyB
    have e : (1 - eta) * share * budget = (1 - eta) * (share * budget) := by ring
    rw [e]
    have e6 : 6 * share * budget * (1 - eta) = 6 * ((1 - eta) * (share * budget)) := by ring
    have : 1 / (2 * ((1 - eta) * (share * budget))) ≤ 5 / (6 * share * budget * (1 - eta)) := by
      rw [e6, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos h0 hy]
    linarith
  · intro epsilon heps
    intro a ha hthr
    obtain ⟨ha0, ha1⟩ := ha
    have hy : 0 < a * budget := by
      by_contra hc; push_neg at hc; nlinarith
    have hyB : a * budget ≤ budget := by nlinarith
    obtain ⟨h1, h2⟩ := g78b_cdiff h0 (by linarith) hy hyB
    have e1 : thermalEntropy budget + thermalEntropy (eta * budget) -
        thermalEntropy ((1 - eta) * budget) -
        (thermalEntropy (a * budget) + thermalEntropy (eta * budget) -
          thermalEntropy ((1 - eta) * a * budget)) =
        ((g budget - g ((1 - eta) * budget)) - (g (a * budget) - g ((1 - eta) * (a * budget))))
          / Real.log 2 := by
      simp only [thermalEntropy, g, mul_assoc]; ring
    rw [e1, abs_div, abs_of_pos hl2, div_le_iff₀ hl2, abs_of_nonneg h1]
    have hB : 0 < budget := lt_of_lt_of_le hy hyB
    have e2 : 5 / (6 * ((1 - eta) * (a * budget))) = epsilon * Real.log 2 := by
      simp only [a]; field_simp
    have : 1 / (2 * ((1 - eta) * (a * budget))) ≤ 5 / (6 * ((1 - eta) * (a * budget))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos h0 hy]
    linarith


end
