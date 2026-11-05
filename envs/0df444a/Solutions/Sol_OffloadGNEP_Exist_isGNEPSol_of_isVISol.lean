-- Prove2me | solution 1 for OffloadGNEP.Exist.isGNEPSol_of_isVISol
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:48:52.275963+00:00
-- url     : https://prove2.me/submissions/9768ff55-f4d4-48d0-bea8-90b7ac9e050d

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

open OffloadGNEP.Exist

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (xb : Fin N → Tier → ℝ) (h : IsVISol (K P) (F P) xb) : IsGNEPSol P xb := by
  obtain ⟨hU0, hU1, hA'⟩ := hA
  obtain ⟨hn, -, -⟩ := hS
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hsumT : ∀ f : Tier → ℝ, ∑ i, f i = f .m + f .clet + f .cloud := by
    intro f
    show ∑ i ∈ ({Tier.m, Tier.clet, Tier.cloud} : Finset Tier), f i = _
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
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
  obtain ⟨hxK, hVI⟩ := h
  refine ⟨hxK, ?_⟩
  intro u y hy hΩ
  set x' := Function.update xb u y with hx'
  have hx'K : x' ∈ K P := by
    refine ⟨fun v => ?_, hΩ⟩
    by_cases hv : v = u
    · subst hv; simpa [x'] using hy
    · simpa [x', Function.update_of_ne hv] using hxK.1 v
  have hV := hVI x' hx'K
  -- reduce the pairing to user `u`'s block
  have hpair : pair (F P xb) (x' - xb) = ∑ i, F P xb u i * (y i - xb u i) := by
    unfold pair
    rw [Finset.sum_eq_single u]
    · simp [x']
    · intro v _ hv
      simp [x', Function.update_of_ne hv]
    · intro hu; exact absurd (Finset.mem_univ u) hu
  rw [hpair, hsumT] at hV
  -- decompose the loads
  set c := ∑ v ∈ Finset.univ.erase u, P.delta v * xb v .clet with hc
  have hload_xb : load P xb = (1 / (P.n : ℝ)) * (P.delta u * xb u .clet + c) := by
    unfold load
    rw [hc, Finset.add_sum_erase Finset.univ (fun v => P.delta v * xb v .clet) (Finset.mem_univ u)]
  have hload_x' : load P x' = (1 / (P.n : ℝ)) * (P.delta u * y .clet + c) := by
    unfold load
    rw [← Finset.add_sum_erase Finset.univ (fun v => P.delta v * x' v .clet) (Finset.mem_univ u), hc]
    congr 2
    · simp [x']
    · apply Finset.sum_congr rfl
      intro v hv
      simp [x', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  have hxu := hxK.1 u
  obtain ⟨hxu0, hxu1, -, -⟩ := hxu
  obtain ⟨hy0, hy1, -, -⟩ := hy
  obtain ⟨ha0, ha1, hd0, hd1⟩ := hA'
    u
  have hD0 : 0 < 1 - load P xb := by
    have := hxK.2; simp only [Omega, Set.mem_ofPred_eq] at this; linarith
  have hD1 : 0 < 1 - load P x' := by
    simp only [Omega, Set.mem_ofPred_eq] at hΩ; linarith
  have hc0 : 0 ≤ c := by
    apply Finset.sum_nonneg; intro v _
    have := (hxK.1 v).1 Tier.clet
    have := (hA' v).2.2.1
    positivity
  have hE : 0 ≤ 1 - (1 / (P.n : ℝ)) * c := by
    have : 0 ≤ (1 / (P.n : ℝ)) * (P.delta u * xb u .clet) := by
      have := hxu0 Tier.clet; positivity
    rw [hload_xb] at hD0; nlinarith
  have hm0 : 0 < 1 - P.alpha u * xb u .m := by
    have := hxu0 .clet; have := hxu0 .cloud; have := hxu0 .m; nlinarith
  have hm1 : 0 < 1 - P.alpha u * y .m := by
    have := hy0 .clet; have := hy0 .cloud; have := hy0 .m; nlinarith
  rw [hload_xb] at hD0
  rw [hload_x'] at hD1
  have i1 := auxm (P.alpha u) (y .m) (xb u .m) hm1 hm0
  have i2 := auxc (P.n : ℝ) (P.delta u) c (y .clet) (xb u .clet) hnR hD0 hD1 hE
  have hFm : F P xb u .m = P.alpha u / (1 - P.alpha u * xb u .m) ^ 2 := rfl
  have hFc : F P xb u .clet = P.beta u + P.delta u * (1 - (1 / (P.n : ℝ)) * c) /
      (1 - (1 / (P.n : ℝ)) * (P.delta u * xb u .clet + c)) ^ 2 := by
    show P.beta u + P.delta u * _ / (1 - load P xb) ^ 2 = _
    rw [hload_xb]
  have hFl : F P xb u .cloud = P.gamma u := rfl
  rw [hFm, hFc, hFl] at hV
  have hcost_xb : cost P u xb = P.alpha u * xb u .m / (1 - P.alpha u * xb u .m) +
      P.beta u * xb u .clet + P.gamma u * xb u .cloud +
      P.delta u * xb u .clet / (1 - (1 / (P.n : ℝ)) * (P.delta u * xb u .clet + c)) := by
    unfold cost; rw [hload_xb]
  have hcost_x' : cost P u x' = P.alpha u * y .m / (1 - P.alpha u * y .m) +
      P.beta u * y .clet + P.gamma u * y .cloud +
      P.delta u * y .clet / (1 - (1 / (P.n : ℝ)) * (P.delta u * y .clet + c)) := by
    unfold cost; rw [hload_x']; simp [x']
  rw [hcost_xb, hcost_x']
  nlinarith [i1, i2, hV]
