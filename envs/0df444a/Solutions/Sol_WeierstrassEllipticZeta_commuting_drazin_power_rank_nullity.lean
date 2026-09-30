-- Prove2me | solution 1 for WeierstrassEllipticZeta.commuting_drazin_power_rank_nullity
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T14:57:19.949444+00:00
-- url     : https://prove2.me/submissions/9831929f-d2a4-44a6-bbfe-d97f04ecf492

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Group.Idempotent



theorem solution
    (K : Type*) [Field K] (n d : ℕ)
    (A B : Matrix (Fin n) (Fin n) K) (hc : Commute A B)
    (h₁ : A * B * B = B) (h₂ : A ^ (d + 1) * B = A ^ d) :
    ∀ N : ℕ, d ≤ N →
      (A ^ N).rank = (A * B).rank ∧
        Module.finrank K (LinearMap.ker (A ^ N).mulVecLin) =
          Module.finrank K (LinearMap.ker (A * B).mulVecLin) := by
  classical
  have he : IsIdempotentElem (A * B) := by
    change (A * B) * (A * B) = A * B
    calc
      (A * B) * (A * B) = (A * (B * A)) * B := by simp only [mul_assoc]
      _ = (A * (A * B)) * B := by rw [← hc.eq]
      _ = A * (A * B * B) := mul_assoc _ _ _
      _ = A * B := by rw [h₁]
  have hfixd : A ^ d * (A * B) = A ^ d := by
    rw [← mul_assoc, ← pow_succ, h₂]
  intro N hN
  have hfactor : A * B = A ^ N * B ^ N := by
    by_cases hzero : N = 0
    · have hd : d = 0 := Nat.eq_zero_of_le_zero (hzero ▸ hN)
      subst d
      subst N
      simpa only [Nat.zero_add, pow_zero, pow_one, one_mul] using h₂
    · calc
        A * B = (A * B) ^ N := (he.pow_eq hzero).symm
        _ = A ^ N * B ^ N := hc.mul_pow N
  have hfix : A ^ N * (A * B) = A ^ N := by
    calc
      A ^ N * (A * B) = (A ^ (N - d) * A ^ d) * (A * B) := by
        rw [← pow_add, Nat.sub_add_cancel hN]
      _ = A ^ (N - d) * (A ^ d * (A * B)) := mul_assoc _ _ _
      _ = A ^ (N - d) * A ^ d := by rw [hfixd]
      _ = A ^ N := by rw [← pow_add, Nat.sub_add_cancel hN]
  have hle₁ := Matrix.rank_mul_le_right (A ^ N) (A * B)
  rw [hfix] at hle₁
  have hle₂ := Matrix.rank_mul_le_left (A ^ N) (B ^ N)
  rw [← hfactor] at hle₂
  have hr : (A ^ N).rank = (A * B).rank := le_antisymm hle₁ hle₂
  refine ⟨hr, ?_⟩
  have hf := LinearMap.finrank_range_add_finrank_ker (A ^ N).mulVecLin
  have hg := LinearMap.finrank_range_add_finrank_ker (A * B).mulVecLin
  change (A ^ N).rank + Module.finrank K (LinearMap.ker (A ^ N).mulVecLin) =
    Module.finrank K (Fin n → K) at hf
  change (A * B).rank + Module.finrank K (LinearMap.ker (A * B).mulVecLin) =
    Module.finrank K (Fin n → K) at hg
  rw [hr] at hf
  exact Nat.add_left_cancel (hf.trans hg.symm)

