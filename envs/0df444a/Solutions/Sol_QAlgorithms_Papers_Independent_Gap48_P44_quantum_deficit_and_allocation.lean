-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.quantum_deficit_and_allocation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:04:08.178922+00:00
-- url     : https://prove2.me/submissions/a8b6e863-829b-4abc-9e88-d6bc5e54f4f6

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

theorem g78b_qdiff {eta x : ℝ} (h0 : 0 < 1 - eta) (h1 : 1 - eta ≤ eta) (hx : 0 < x) :
    0 ≤ Real.log eta - Real.log (1 - eta) - (g (eta * x) - g ((1 - eta) * x)) ∧
    Real.log eta - Real.log (1 - eta) - (g (eta * x) - g ((1 - eta) * x)) ≤
      1 / ((1 - eta) * x) := by
  have he : 0 < eta := by linarith
  have ha : 0 < eta * x := by positivity
  have hb : 0 < (1 - eta) * x := by positivity
  have A := g78b_hh_anti hb ha (by nlinarith)
  have B1 := g78b_hh_ge ha
  have B2 := g78b_hh_le hb
  simp only at A
  rw [g78b_g_eq ha, g78b_g_eq hb]
  generalize (eta * x + 1) * (Real.log (eta * x + 1) - Real.log (eta * x)) = H1 at *
  generalize ((1 - eta) * x + 1) * (Real.log ((1 - eta) * x + 1) - Real.log ((1 - eta) * x)) = H2 at *
  rw [Real.log_mul he.ne' hx.ne', Real.log_mul h0.ne' hx.ne']
  constructor <;> linarith

/-- PDF pp.7,9, Proposition 5: both the nats bound and the feasible photon
allocation giving an epsilon-bit deficit from the LIMITING quantum benchmark.
This does not identify a finite-budget operational capacity with that limit. -/
theorem solution (eta budget : ℝ)
    (heta : 1 - eta ≤ eta) (heta1 : eta < 1)
    (hbudget : 0 ≤ budget) (hthreshold : 2 ≤ (1 - eta) * budget) :
    (Real.log eta - Real.log (1 - eta) - 1 / (eta * (1 - eta) * budget) ≤
      g (eta * budget) - g ((1 - eta) * budget)) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      let share := 1 / (eta * (1 - eta) * epsilon * budget * Real.log 2)
      share ∈ Set.Icc (0 : ℝ) 1 → 2 ≤ share * (1 - eta) * budget →
      |(Real.log eta - Real.log (1 - eta)) / Real.log 2 -
        (thermalEntropy (eta * share * budget) -
          thermalEntropy ((1 - eta) * share * budget))| ≤ epsilon) := by
  have h0 : 0 < 1 - eta := by linarith
  have he : 0 < eta := by linarith
  have hB : 0 < budget := by
    by_contra hc; push_neg at hc; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_⟩
  · obtain ⟨_, h2⟩ := g78b_qdiff h0 heta hB
    have : 1 / ((1 - eta) * budget) ≤ 1 / (eta * (1 - eta) * budget) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_pos h0 hB]
    linarith
  · intro epsilon heps
    intro share hshare hthr
    have hx : 0 < share * budget := by
      by_contra hc; push_neg at hc; nlinarith
    obtain ⟨h1, h2⟩ := g78b_qdiff h0 heta hx
    have e1 : thermalEntropy (eta * share * budget) - thermalEntropy ((1 - eta) * share * budget)
        = (g (eta * (share * budget)) - g ((1 - eta) * (share * budget))) / Real.log 2 := by
      simp only [thermalEntropy, g, mul_assoc]; ring
    rw [e1, ← sub_div, abs_div, abs_of_pos hl2, div_le_iff₀ hl2, abs_of_nonneg h1]
    have e2 : share * budget = 1 / (eta * (1 - eta) * epsilon * Real.log 2) := by
      simp only [share]; field_simp
    have : 1 / ((1 - eta) * (share * budget)) ≤ 1 / (eta * (1 - eta) * (share * budget)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_pos h0 hx]
    have e3 : 1 / (eta * (1 - eta) * (share * budget)) = epsilon * Real.log 2 := by
      rw [e2]; field_simp
    linarith


end
