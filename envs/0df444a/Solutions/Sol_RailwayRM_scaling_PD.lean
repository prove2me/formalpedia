-- Prove2me | solution 1 for RailwayRM.scaling_PD
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:22:57.534185+00:00
-- url     : https://prove2.me/submissions/bacc2aa8-f2a4-46e3-be51-7eb8474ac862

import Mathlib
import Definitions.Def_RailwayRM_Model

open RailwayRM in
theorem solution {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (κ : ℕ+) :
    (I.scale κ).IsOptimalD v (scaleCoaches κ b) ∧
      (I.scale κ).detProfit v (scaleCoaches κ b) = ((κ : ℕ) : ℝ) * I.detProfit v b := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ((κ : ℕ) : ℝ) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < c := by rw [hcdef]; exact Nat.cast_pos.mpr κ.pos
  have hT : (((I.scale κ).T : ℕ) : ℝ) = c * I.T := by
    rw [hcdef]; show (((κ : ℕ) * I.T : ℕ) : ℝ) = _; push_cast; ring
  have hprof : ∀ (v : Rates M N) (b : Fin M → ℝ),
      (I.scale κ).detProfit v (scaleCoaches κ b) = c * I.detProfit v b := by
    intro v b
    have hco : (I.scale κ).co = I.co := rfl
    have hcs : (I.scale κ).cs = I.cs := rfl
    have hk : (I.scale κ).k = I.k := rfl
    have hxm : ∀ m, (I.scale κ).xbarMax v m = I.xbarMax v m := fun m => rfl
    have hy : ∀ ℓ m, (I.scale κ).ybar v ℓ m = I.ybar v ℓ m := fun ℓ m => rfl
    have hr : (I.scale κ).rbar v = I.rbar v := rfl
    have hsc : ∀ m, scaleCoaches κ b m = c * b m := fun m => by rw [hcdef]; rfl
    simp only [Instance.detProfit, Instance.detRevenue, Instance.detCost, hT, hco, hcs, hk, hxm,
      hy, hr, hsc]
    have e1 : ∑ m, I.co * (c * b m) = c * ∑ m, I.co * b m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    have e2 : ∑ m, I.co * (c * (I.T : ℝ)) / (I.k : ℝ) * I.xbarMax v m =
        c * ∑ m, I.co * (I.T : ℝ) / (I.k : ℝ) * I.xbarMax v m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)
    have hm : ∀ X : ℝ, max (c * X) 0 = c * max X 0 := fun X => by
      rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
    have e3 : ∑ m, ∑ ℓ : Fin L, I.cs * max (I.ybar v ℓ m * (c * (I.T : ℝ)) - c * b m * (I.k : ℝ)) 0
        = c * ∑ m, ∑ ℓ : Fin L, I.cs * max (I.ybar v ℓ m * (I.T : ℝ) - b m * (I.k : ℝ)) 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [show I.ybar v ℓ m * (c * (I.T : ℝ)) - c * b m * (I.k : ℝ)
          = c * (I.ybar v ℓ m * (I.T : ℝ) - b m * (I.k : ℝ)) by ring, hm]
      ring
    rw [e1, e2, e3]
    ring
  have hfeas : (I.scale κ).IsFeasibleD v (scaleCoaches κ b) := by
    obtain ⟨hv, hb, hcap⟩ := hopt.1
    refine ⟨hv, fun m => ⟨?_, ?_⟩, fun ℓ m => ?_⟩
    · show 0 ≤ ((κ : ℕ) : ℝ) * b m
      rw [← hcdef]; exact mul_nonneg hc.le (hb m).1
    · show ((((κ : ℕ) * I.bMin m : ℕ)) : ℝ) ≤ ((κ : ℕ) : ℝ) * b m
      push_cast
      rw [← hcdef]
      exact mul_le_mul_of_nonneg_left (hb m).2 hc.le
    · show I.xbar v ℓ m * (((I.scale κ).T : ℕ) : ℝ) + ((κ : ℕ) : ℝ) * b m * (I.k : ℝ) ≤
        ((((κ : ℕ) * I.bMax m : ℕ)) : ℝ) * (I.k : ℝ)
      rw [hT]
      push_cast
      rw [← hcdef]
      nlinarith [mul_le_mul_of_nonneg_left (hcap ℓ m) hc.le]
  refine ⟨⟨hfeas, fun v' b' hf' => ?_⟩, by rw [hprof, hcdef]⟩
  obtain ⟨hv', hb', hcap'⟩ := hf'
  have hfeas' : I.IsFeasibleD v' (fun m => b' m / c) := by
    refine ⟨hv', fun m => ⟨div_nonneg (hb' m).1 hc.le, ?_⟩, fun ℓ m => ?_⟩
    · have h := (hb' m).2
      change ((((κ : ℕ) * I.bMin m : ℕ)) : ℝ) ≤ b' m at h
      push_cast at h
      rw [← hcdef] at h
      rw [le_div_iff₀ hc]
      linarith
    · have h := hcap' ℓ m
      change I.xbar v' ℓ m * (((I.scale κ).T : ℕ) : ℝ) + b' m * (I.k : ℝ) ≤
        ((((κ : ℕ) * I.bMax m : ℕ)) : ℝ) * (I.k : ℝ) at h
      rw [hT] at h
      push_cast at h
      rw [← hcdef] at h
      have hq : b' m = c * (b' m / c) := by field_simp
      rw [hq] at h
      simp only
      nlinarith
  have h1 := hopt.2 v' (fun m => b' m / c) hfeas'
  have h2 : (I.scale κ).detProfit v' b' = c * I.detProfit v' (fun m => b' m / c) := by
    rw [← hprof v' (fun m => b' m / c)]
    congr 1
    funext m
    show b' m = ((κ : ℕ) : ℝ) * (b' m / c)
    rw [← hcdef]
    field_simp
  rw [h2, hprof]
  exact mul_le_mul_of_nonneg_left h1 hc.le
