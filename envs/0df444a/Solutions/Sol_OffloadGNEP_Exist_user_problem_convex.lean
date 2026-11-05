-- Prove2me | solution 1 for OffloadGNEP.Exist.user_problem_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:53:10.256199+00:00
-- url     : https://prove2.me/submissions/0f29c6c5-6904-42df-8341-e86a8441d988

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

open OffloadGNEP.Exist

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (u : Fin N) (x : Fin N → Tier → ℝ) :
    Convex ℝ {y ∈ Ktil P u | Function.update x u y ∈ Omega P} ∧
      ConvexOn ℝ {y ∈ Ktil P u | Function.update x u y ∈ Omega P}
        (fun y => cost P u (Function.update x u y)) := by
  obtain ⟨hU0, hU1, hA'⟩ := hA
  obtain ⟨hn, -, -⟩ := hS
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  obtain ⟨ha0, ha1, hd0, hd1⟩ := hA' u
  -- convexity inequality for the device term
  have auxm : ∀ α s t : ℝ, 0 < 1 - α * s → 0 < 1 - α * t →
      α * t / (1 - α * t) + α / (1 - α * t) ^ 2 * (s - t) ≤ α * s / (1 - α * s) := by
    intro α s t hA hB
    have key : α * s / (1 - α * s) - (α * t / (1 - α * t) + α / (1 - α * t) ^ 2 * (s - t)) =
        (α * (s - t)) ^ 2 / ((1 - α * s) * (1 - α * t) ^ 2) := by
      field_simp; ring
    have : 0 ≤ (α * (s - t)) ^ 2 / ((1 - α * s) * (1 - α * t) ^ 2) := by positivity
    linarith
  -- convexity inequality for the cloudlet congestion term
  have auxc : ∀ n δ c s t : ℝ, 0 < n → 0 < 1 - (1 / n) * (δ * t + c) →
      0 < 1 - (1 / n) * (δ * s + c) → 0 ≤ 1 - (1 / n) * c →
      δ * t / (1 - (1 / n) * (δ * t + c)) +
          δ * (1 - (1 / n) * c) / (1 - (1 / n) * (δ * t + c)) ^ 2 * (s - t) ≤
        δ * s / (1 - (1 / n) * (δ * s + c)) := by
    intro n δ c s t hn h0 h1 hE
    generalize hD0 : 1 - (1 / n) * (δ * t + c) = D0 at *
    generalize hD1 : 1 - (1 / n) * (δ * s + c) = D1 at *
    generalize hEE : 1 - (1 / n) * c = E at *
    have et : δ * t = n * (E - D0) := by rw [← hD0, ← hEE]; field_simp; ring
    have es : δ * s = n * (E - D1) := by rw [← hD1, ← hEE]; field_simp; ring
    have est : δ * (s - t) = n * (D0 - D1) := by linear_combination es - et
    rw [show δ * E / D0 ^ 2 * (s - t) = E * (δ * (s - t)) / D0 ^ 2 by ring, est, et, es]
    have key : n * (E - D1) / D1 - (n * (E - D0) / D0 + E * (n * (D0 - D1)) / D0 ^ 2) =
        n * E * (D0 - D1) ^ 2 / (D0 ^ 2 * D1) := by
      field_simp; ring
    have : 0 ≤ n * E * (D0 - D1) ^ 2 / (D0 ^ 2 * D1) := by
      apply div_nonneg (mul_nonneg (mul_nonneg hn.le hE) (sq_nonneg _)); positivity
    linarith
  -- combining two tangent inequalities at a convex combination
  have comb : ∀ fs fs' ft d s s' a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ft + d * (s - (a * s + b * s')) ≤ fs → ft + d * (s' - (a * s + b * s')) ≤ fs' →
      ft ≤ a * fs + b * fs' := by
    intro fs fs' ft d s s' a b ha hb hab h1 h2
    obtain rfl : b = 1 - a := by linarith
    linear_combination (mul_le_mul_of_nonneg_left h1 ha) + (mul_le_mul_of_nonneg_left h2 hb)
  -- decomposition of the load and the cost
  set c := ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet with hc
  have hload : ∀ z, load P (Function.update x u z) = (1 / (P.n : ℝ)) * (P.delta u * z .clet + c) := by
    intro z
    unfold load
    rw [← Finset.add_sum_erase Finset.univ
      (fun v => P.delta v * Function.update x u z v .clet) (Finset.mem_univ u), hc]
    congr 2
    · simp
    · apply Finset.sum_congr rfl
      intro v hv
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  have hcost : ∀ z, cost P u (Function.update x u z) = P.alpha u * z .m / (1 - P.alpha u * z .m) +
      P.beta u * z .clet + P.gamma u * z .cloud +
      P.delta u * z .clet / (1 - (1 / (P.n : ℝ)) * (P.delta u * z .clet + c)) := by
    intro z; unfold cost; rw [hload]; simp
  have hlin : ∀ (y z : Tier → ℝ) (a b : ℝ),
      load P (Function.update x u (a • y + b • z)) =
        (1 / (P.n : ℝ)) * (P.delta u * (a * y .clet + b * z .clet) + c) := by
    intro y z a b; rw [hload]; simp
  -- facts at feasible points
  have hfeas : ∀ z, z ∈ {y ∈ Ktil P u | Function.update x u y ∈ Omega P} →
      0 < 1 - P.alpha u * z .m ∧ 0 < 1 - (1 / (P.n : ℝ)) * (P.delta u * z .clet + c) ∧
      0 ≤ 1 - (1 / (P.n : ℝ)) * c := by
    rintro z ⟨⟨h0, h1, -, -⟩, hΩ⟩
    simp only [Omega, Set.mem_ofPred_eq, hload] at hΩ
    have := h0 .m; have := h0 .clet; have := h0 .cloud
    refine ⟨by nlinarith, by linarith, ?_⟩
    have : 0 ≤ (1 / (P.n : ℝ)) * (P.delta u * z .clet) := by positivity
    nlinarith
  have hconv : Convex ℝ {y ∈ Ktil P u | Function.update x u y ∈ Omega P} := by
    rintro y ⟨⟨hy0, hy1, hy2, hy3⟩, hyΩ⟩ z ⟨⟨hz0, hz1, hz2, hz3⟩, hzΩ⟩ a b ha hb hab
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hy0 i; have := hz0 i; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hy1 + b * hz1 + hab
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (mul_le_mul_of_nonneg_left hy2 ha) + (mul_le_mul_of_nonneg_left hz2 hb) +
          P.chi * hab
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (mul_le_mul_of_nonneg_left hy3 ha) + (mul_le_mul_of_nonneg_left hz3 hb) +
          P.Pmax u * hab
    · simp only [Omega, Set.mem_ofPred_eq, hload] at hyΩ hzΩ ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (mul_le_mul_of_nonneg_left hyΩ ha) + (mul_le_mul_of_nonneg_left hzΩ hb) +
          (P.Umax - 1 / (P.n : ℝ) * c) * hab
  refine ⟨hconv, hconv, ?_⟩
  intro y hy z hz a b ha hb hab
  have hw := hconv hy hz ha hb hab
  set w := a • y + b • z with hwdef
  have hwm : w .m = a * y .m + b * z .m := by simp [hwdef]
  have hwc : w .clet = a * y .clet + b * z .clet := by simp [hwdef]
  have hwl : w .cloud = a * y .cloud + b * z .cloud := by simp [hwdef]
  obtain ⟨fy1, fy2, -⟩ := hfeas y hy
  obtain ⟨fz1, fz2, -⟩ := hfeas z hz
  obtain ⟨fw1, fw2, fw3⟩ := hfeas w hw
  simp only [smul_eq_mul]
  rw [hcost, hcost, hcost]
  have m1 := auxm (P.alpha u) (y .m) (w .m) fy1 fw1
  have m2 := auxm (P.alpha u) (z .m) (w .m) fz1 fw1
  have c1 := auxc (P.n : ℝ) (P.delta u) c (y .clet) (w .clet) hnR fw2 fy2 fw3
  have c2 := auxc (P.n : ℝ) (P.delta u) c (z .clet) (w .clet) hnR fw2 fz2 fw3
  rw [hwm] at m1 m2 ⊢
  rw [hwc] at c1 c2 ⊢
  rw [hwl]
  have e1 := comb _ _ _ _ _ _ a b ha hb hab m1 m2
  have e2 := comb _ _ _ _ _ _ a b ha hb hab c1 c2
  nlinarith [e1, e2]
