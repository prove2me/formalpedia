-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P24.lowerBoundConvex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:20:55.936065+00:00
-- url     : https://prove2.me/submissions/e63962e6-8882-488b-8210-247c7aa635e6

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)

open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma s110lb_g_cont : Continuous g := by
  unfold g
  exact (Real.continuous_mul_log.comp (continuous_id.add continuous_const)).sub
    Real.continuous_mul_log

lemma s110lb_g_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt g (Real.log (x + 1) - Real.log x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
  have h2 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x :=
    h1.log (by linarith)
  have h3 : HasDerivAt (fun y : ℝ => (y + 1) * Real.log (y + 1))
      (1 * Real.log (x + 1) + (x + 1) * (1 / (x + 1))) x := h1.mul h2
  have h4 : HasDerivAt (fun y : ℝ => y * Real.log y)
      (1 * Real.log x + x * x⁻¹) x := (hasDerivAt_id' x).mul (Real.hasDerivAt_log hx.ne')
  have e1 : (x + 1) * (1 / (x + 1)) = 1 := by field_simp
  have e2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  rw [e1] at h3
  rw [e2] at h4
  have := h3.sub h4
  have hfun : g = fun y : ℝ => (y + 1) * Real.log (y + 1) - y * Real.log y := by
    funext y; rfl
  rw [hfun]
  exact this.congr_deriv (by ring)

lemma s110lb_phi_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (y + 1) - Real.log y) (1 / (x + 1) - 1 / x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
  have h2 : HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x :=
    h1.log (by linarith)
  have h3 := Real.hasDerivAt_log hx.ne'
  exact (h2.sub h3).congr_deriv (by simp [one_div])

lemma s110lb_g_mono : MonotoneOn g (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) s110lb_g_cont.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    exact (s110lb_g_deriv hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(s110lb_g_deriv hx).deriv]
    have : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx (by linarith)
    linarith

end QAlgorithms.Papers.Independent.Advance50.P24

open QAlgorithms.Papers.Independent.Advance50.P24
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

theorem solution (N : ℝ) (hN : 0 < N) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun eta => lowerBound eta N) := by
  set h : ℝ → ℝ := fun eta => g (eta * N) - g ((1 - eta) * N) with hh
  set φ : ℝ → ℝ := fun y => Real.log (y + 1) - Real.log y with hφ
  set D : ℝ → ℝ := fun eta => N * φ (eta * N) - N * φ ((1 - eta) * N) * (-1) with hD
  have hcont : Continuous h :=
    (s110lb_g_cont.comp (continuous_id.mul continuous_const)).sub
      (s110lb_g_cont.comp ((continuous_const.sub continuous_id).mul continuous_const))
  have hderiv : ∀ eta ∈ Set.Ioo (1/2 : ℝ) 1, HasDerivAt h (D eta) eta := by
    intro eta he
    have ha : 0 < eta * N := mul_pos (by linarith [he.1]) hN
    have hb : 0 < (1 - eta) * N := mul_pos (by linarith [he.2]) hN
    have d1 : HasDerivAt (fun e : ℝ => e * N) N eta := by
      simpa using (hasDerivAt_id eta).mul_const N
    have d2 : HasDerivAt (fun e : ℝ => (1 - e) * N) (-N) eta := by
      simpa using ((hasDerivAt_id eta).const_sub 1).mul_const N
    have := ((s110lb_g_deriv ha).comp eta d1).sub ((s110lb_g_deriv hb).comp eta d2)
    exact this.congr_deriv (by simp only [hD, hφ]; ring)
  have hDderiv : ∀ eta ∈ Set.Ioo (1/2 : ℝ) 1,
      HasDerivAt D (N * (1 / (eta * N + 1) - 1 / (eta * N)) * N
        - N * (1 / ((1 - eta) * N + 1) - 1 / ((1 - eta) * N)) * (-N) * (-1)) eta := by
    intro eta he
    have ha : 0 < eta * N := mul_pos (by linarith [he.1]) hN
    have hb : 0 < (1 - eta) * N := mul_pos (by linarith [he.2]) hN
    have d1 : HasDerivAt (fun e : ℝ => e * N) N eta := by
      simpa using (hasDerivAt_id eta).mul_const N
    have d2 : HasDerivAt (fun e : ℝ => (1 - e) * N) (-N) eta := by
      simpa using ((hasDerivAt_id eta).const_sub 1).mul_const N
    have e1 := (((s110lb_phi_deriv ha).comp eta d1).const_mul N)
    have e2 := ((((s110lb_phi_deriv hb).comp eta d2).const_mul N).mul_const (-1 : ℝ))
    exact (e1.sub e2).congr_deriv (by ring)
  -- convexity of h on [1/2,1]
  have hconv : ConvexOn ℝ (Set.Icc (1/2 : ℝ) 1) h := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _) hcont.continuousOn
    · rw [interior_Icc]
      intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      have hmD : MonotoneOn D (Set.Ioo (1/2 : ℝ) 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
        · intro x hx; exact (hDderiv x hx).continuousAt.continuousWithinAt
        · rw [interior_Ioo]; intro x hx
          exact (hDderiv x hx).differentiableAt.differentiableWithinAt
        · rw [interior_Ioo]; intro x hx
          rw [(hDderiv x hx).deriv]
          have ha : 0 < x * N := mul_pos (by linarith [hx.1]) hN
          have hb : 0 < (1 - x) * N := mul_pos (by linarith [hx.2]) hN
          have hab : (1 - x) * N ≤ x * N := by nlinarith [hx.1]
          set a := x * N
          set b := (1 - x) * N
          have key : 0 ≤ (1 / b - 1 / a) - (1 / (b + 1) - 1 / (a + 1)) := by
            rw [div_sub_div _ _ hb.ne' ha.ne', div_sub_div _ _ (by linarith) (by linarith)]
            have hn : 0 ≤ (1 * a - b * 1) := by linarith
            rw [sub_nonneg]
            apply div_le_div₀ (by linarith) (by linarith) (by positivity)
            nlinarith
          have : 0 ≤ N * N * ((1 / b - 1 / a) - (1 / (b + 1) - 1 / (a + 1))) :=
            mul_nonneg (mul_nonneg hN.le hN.le) key
          nlinarith [this]
      intro x hx y hy hxy
      rw [(hderiv x hx).deriv, (hderiv y hy).deriv]
      exact hmD hx hy hxy
  have hmono : MonotoneOn h (Set.Icc (1/2 : ℝ) 1) := by
    intro x hx y hy hxy
    simp only [hh]
    have h1 : g (x * N) ≤ g (y * N) :=
      s110lb_g_mono (show (0:ℝ) ≤ x * N by nlinarith [hx.1])
        (show (0:ℝ) ≤ y * N by nlinarith [hy.1]) (by nlinarith)
    have h2 : g ((1 - y) * N) ≤ g ((1 - x) * N) :=
      s110lb_g_mono (show (0:ℝ) ≤ (1 - y) * N by nlinarith [hy.2])
        (show (0:ℝ) ≤ (1 - x) * N by nlinarith [hx.2]) (by nlinarith)
    linarith
  have hrep : ∀ eta, lowerBound eta N = h (max eta (1/2)) := by
    intro eta
    unfold lowerBound
    split_ifs with he
    · rw [max_eq_left he.le]
    · rw [max_eq_right (not_lt.mp he)]
      simp only [hh]
      norm_num
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [hrep, smul_eq_mul]
  have mx : max x (1/2) ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_max_right _ _, max_le hx.2 (by norm_num)⟩
  have my : max y (1/2) ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_max_right _ _, max_le hy.2 (by norm_num)⟩
  have mz : a * max x (1/2) + b * max y (1/2) ∈ Set.Icc (1/2 : ℝ) 1 := by
    have := (convex_Icc (1/2 : ℝ) 1) mx my ha hb hab
    simpa [smul_eq_mul] using this
  have mle : max (a * x + b * y) (1/2) ≤ a * max x (1/2) + b * max y (1/2) := by
    apply max_le
    · nlinarith [le_max_left x (1/2), le_max_left y (1/2)]
    · nlinarith [le_max_right x (1/2), le_max_right y (1/2)]
  have mw : max (a * x + b * y) (1/2) ∈ Set.Icc (1/2 : ℝ) 1 :=
    ⟨le_max_right _ _, le_trans mle mz.2⟩
  calc h (max (a * x + b * y) (1/2)) ≤ h (a * max x (1/2) + b * max y (1/2)) :=
        hmono mw mz mle
    _ ≤ a * h (max x (1/2)) + b * h (max y (1/2)) := by
        simpa [smul_eq_mul] using hconv.2 mx my ha hb hab

end
