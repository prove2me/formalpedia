-- Prove2me | solution 1 for UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7de3da6a-a774-5a16-b378-7bf9dc4f4a8d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval

set_option autoImplicit false

open Polynomial UnramifiedWhittaker

namespace RS9

section Algebra

variable {R : Type*} [CommRing R]

theorem mul_mul_recursion_of_recursion (s p s' p' : R) (h h' : ℕ → R)
    (hh : ∀ m, h (m + 2) = s * h (m + 1) - p * h m)
    (hh' : ∀ m, h' (m + 2) = s' * h' (m + 1) - p' * h' m) (m : ℕ) :
    h (m + 4) * h' (m + 4) =
      s * s' * (h (m + 3) * h' (m + 3))
        - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * (h (m + 2) * h' (m + 2))
        + s * s' * p * p' * (h (m + 1) * h' (m + 1))
        - p ^ 2 * p' ^ 2 * (h m * h' m) := by
  have e2 : h (m + 2) = s * h (m + 1) - p * h m := hh m
  have e3 : h (m + 3) = s * h (m + 2) - p * h (m + 1) := hh (m + 1)
  have e4 : h (m + 4) = s * h (m + 3) - p * h (m + 2) := hh (m + 2)
  have f2 : h' (m + 2) = s' * h' (m + 1) - p' * h' m := hh' m
  have f3 : h' (m + 3) = s' * h' (m + 2) - p' * h' (m + 1) := hh' (m + 1)
  have f4 : h' (m + 4) = s' * h' (m + 3) - p' * h' (m + 2) := hh' (m + 2)
  rw [e4, f4, e3, f3, e2, f2]
  ring

theorem rsEulerPoly_zero_eq_prod (x₁ x₂ y₁ y₂ : R) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly (x₁ + x₂) (x₁ * x₂) (y₁ + y₂) (y₁ * y₂) 0 =
      (C 1 - C (x₁ * y₁) * X) * (C 1 - C (x₁ * y₂) * X) *
        ((C 1 - C (x₂ * y₁) * X) * (C 1 - C (x₂ * y₂) * X)) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat, map_one, map_zero]
  ring

theorem eval_rsEulerPoly_zero (s p s' p' x : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly s p s' p' 0).eval x =
      1 - s * s' * x + (s ^ 2 * p' + p * s' ^ 2 - 2 * p * p') * x ^ 2
        - s * p * s' * p' * x ^ 3 + p ^ 2 * p' ^ 2 * x ^ 4 := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

theorem eval_rsEulerPoly_scale (c a b e₁ e₂ e₃ x : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (c * a) (c ^ 2 * b) e₁ e₂ e₃).eval x =
      (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).eval (c * x) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

end Algebra

section Analytic

theorem tsum_mul_mul_pow_mul_eval_rsEulerPoly (s p s' p' : ℂ) (h h' : ℕ → ℂ)
    (h0 : h 0 = 1) (h1 : h 1 = s) (h0' : h' 0 = 1) (h1' : h' 1 = s')
    (hh : ∀ m, h (m + 2) = s * h (m + 1) - p * h m)
    (hh' : ∀ m, h' (m + 2) = s' * h' (m + 1) - p' * h' m)
    (x : ℂ) (hsum : Summable fun m : ℕ => h m * h' m * x ^ m) :
    (∑' m : ℕ, h m * h' m * x ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly s p s' p' 0).eval x =
      1 - p * p' * x ^ 2 := by
  set c : ℕ → ℂ := fun m => h m * h' m * x ^ m with hc

  have tail : ∀ k : ℕ, ∑' m, c (m + k) = (∑' m, c m) - ∑ i ∈ Finset.range k, c i := by
    intro k
    have := hsum.sum_add_tsum_nat_add k
    linear_combination this
  have hs : ∀ k : ℕ, Summable fun m => c (m + k) := fun k => (summable_nat_add_iff k).mpr hsum

  have hrec : ∀ m, c (m + 4) = s * s' * x * c (m + 3) - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * x ^ 2 * c (m + 2)
      + s * s' * p * p' * x ^ 3 * c (m + 1) - p ^ 2 * p' ^ 2 * x ^ 4 * c m := by
    intro m
    have key := mul_mul_recursion_of_recursion s p s' p' h h' hh hh' m
    simp only [hc]
    rw [key]
    ring
  have T4 : ∑' m, c (m + 4) =
      s * s' * x * ∑' m, c (m + 3) - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * x ^ 2 * ∑' m, c (m + 2)
        + s * s' * p * p' * x ^ 3 * ∑' m, c (m + 1) - p ^ 2 * p' ^ 2 * x ^ 4 * ∑' m, c m := by
    rw [show (fun m => c (m + 4)) = fun m =>
        s * s' * x * c (m + 3) - (s ^ 2 * p' + s' ^ 2 * p - 2 * p * p') * x ^ 2 * c (m + 2)
          + s * s' * p * p' * x ^ 3 * c (m + 1) - p ^ 2 * p' ^ 2 * x ^ 4 * c m from funext hrec]
    rw [((((hs 3).mul_left _).sub ((hs 2).mul_left _)).add ((hs 1).mul_left _)).tsum_sub
        (hsum.mul_left _)]
    rw [(((hs 3).mul_left _).sub ((hs 2).mul_left _)).tsum_add ((hs 1).mul_left _)]
    rw [((hs 3).mul_left _).tsum_sub ((hs 2).mul_left _)]
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [tail 4, tail 3, tail 2, tail 1] at T4
  have h2 : h 2 = s * s - p := by rw [hh 0, h1, h0]; ring
  have h3 : h 3 = s * (s * s - p) - p * s := by rw [hh 1, h2, h1]
  have h2' : h' 2 = s' * s' - p' := by rw [hh' 0, h1', h0']; ring
  have h3' : h' 3 = s' * (s' * s' - p') - p' * s' := by rw [hh' 1, h2', h1']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, h0, h1, h2, h3, h0', h1', h2', h3',
    zero_add, pow_zero, pow_one] at T4
  rw [eval_rsEulerPoly_zero]
  linear_combination T4

theorem pow_mul_heckeRecursionSeq_rec (N lam om : ℂ) (hN : N ≠ 0) :
    (N ^ 0 * heckeRecursionSeq N lam om 0 = 1) ∧ (N ^ 1 * heckeRecursionSeq N lam om 1 = lam) ∧
      ∀ m, N ^ (m + 2) * heckeRecursionSeq N lam om (m + 2) =
        lam * (N ^ (m + 1) * heckeRecursionSeq N lam om (m + 1))
          - N * om * (N ^ m * heckeRecursionSeq N lam om m) := by
  refine ⟨by simp [heckeRecursionSeq], by rw [heckeRecursionSeq, pow_one]; field_simp, fun m => ?_⟩
  rw [heckeRecursionSeq]
  field_simp
  ring

theorem tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_eval_rsEulerPoly
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hsum : Summable fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly lam (N * om) lam' (N * om') 0).eval (y / N ^ 2) =
      1 - om * om' * (y / N) ^ 2 := by
  obtain ⟨a0, a1, ha⟩ := pow_mul_heckeRecursionSeq_rec N lam om hN
  obtain ⟨b0, b1, hb⟩ := pow_mul_heckeRecursionSeq_rec N lam' om' hN
  have hfun : (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) =
      fun m : ℕ => (N ^ m * heckeRecursionSeq N lam om m) * (N ^ m * heckeRecursionSeq N lam' om' m) *
        (y / N ^ 2) ^ m := by
    funext m
    rw [div_pow, ← pow_mul, mul_comm 2 m, pow_mul]
    field_simp
  rw [hfun] at hsum ⊢
  rw [tsum_mul_mul_pow_mul_eval_rsEulerPoly lam (N * om) lam' (N * om') _ _ a0 a1 b0 b1 ha hb _ hsum]
  field_simp

theorem conj_heckeRecursionSeq (N lam om : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (heckeRecursionSeq N lam om m) =
      heckeRecursionSeq ((starRingEnd ℂ) N) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [heckeRecursionSeq]
    | 1, _ => simp [heckeRecursionSeq]
    | m + 2, ih =>
      rw [heckeRecursionSeq, heckeRecursionSeq, map_div₀, map_sub, map_mul, map_mul,
        ih (m + 1) (by omega), ih m (by omega)]

theorem norm_pow_mul_heckeRecursionSeq_le (N lam om : ℂ) (hN : N ≠ 0) (m : ℕ) :
    ‖N ^ m * heckeRecursionSeq N lam om m‖ ≤ (max 1 (‖lam‖ + ‖N * om‖)) ^ m := by
  obtain ⟨a0, a1, ha⟩ := pow_mul_heckeRecursionSeq_rec N lam om hN
  set M := max 1 (‖lam‖ + ‖N * om‖) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hlam : ‖lam‖ ≤ M := le_trans (le_add_of_nonneg_right (norm_nonneg _)) (le_max_right _ _)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [heckeRecursionSeq]
    | 1, _ => rw [a1, pow_one]; exact hlam
    | m + 2, ih =>
      rw [ha m]
      have i1 := ih (m + 1) (by omega)
      have i0 := ih m (by omega)
      calc ‖lam * (N ^ (m + 1) * heckeRecursionSeq N lam om (m + 1)) -
              N * om * (N ^ m * heckeRecursionSeq N lam om m)‖
          ≤ ‖lam‖ * M ^ (m + 1) + ‖N * om‖ * M ^ m := by
            refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]; exact mul_le_mul_of_nonneg_left i1 (norm_nonneg _)
            · rw [norm_mul]; exact mul_le_mul_of_nonneg_left i0 (norm_nonneg _)
        _ ≤ ‖lam‖ * M ^ (m + 1) + ‖N * om‖ * M ^ (m + 1) := by
            have hp : M ^ m ≤ M ^ (m + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ m)
            have := mul_le_mul_of_nonneg_left hp (norm_nonneg (N * om))
            linarith
        _ = (‖lam‖ + ‖N * om‖) * M ^ (m + 1) := by ring
        _ ≤ M * M ^ (m + 1) := by gcongr; exact le_max_right _ _
        _ = M ^ (m + 2) := by ring

theorem summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hy : ‖y‖ * (max 1 (‖lam‖ + ‖N * om‖)) * (max 1 (‖lam'‖ + ‖N * om'‖)) < ‖N‖ ^ 2) :
    Summable fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m := by
  set M := max 1 (‖lam‖ + ‖N * om‖)
  set M' := max 1 (‖lam'‖ + ‖N * om'‖)
  have hNn : 0 < ‖N‖ ^ 2 := by positivity
  set r : ℝ := ‖y‖ * M * M' / ‖N‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hNn]; exact hy
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr1) (fun m => ?_)
  have e : heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m =
      (N ^ m * heckeRecursionSeq N lam om m) * (N ^ m * heckeRecursionSeq N lam' om' m) * (y / N ^ 2) ^ m := by
    rw [div_pow, ← pow_mul, mul_comm 2 m, pow_mul]
    field_simp
  rw [e, norm_mul, norm_mul, norm_pow, norm_div, norm_pow, hr,
    show (‖y‖ * M * M' / ‖N‖ ^ 2) ^ m = M ^ m * M' ^ m * (‖y‖ / ‖N‖ ^ 2) ^ m by ring]
  have b1 := norm_pow_mul_heckeRecursionSeq_le N lam om hN m
  have b2 := norm_pow_mul_heckeRecursionSeq_le N lam' om' hN m
  have : ‖N ^ m * heckeRecursionSeq N lam om m‖ * ‖N ^ m * heckeRecursionSeq N lam' om' m‖ ≤ M ^ m * M' ^ m :=
    mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  gcongr

end Analytic

end RS9

theorem solution
    (N lam om lam' om' : ℂ) (hN : N ≠ 0) (y : ℂ)
    (hsum : Summable fun m : ℕ =>
      heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * y ^ m) *
        (LanglandsTunnell.RankinSelberg.rsEulerPoly lam (N * om) lam' (N * om') 0).eval (y / N ^ 2) =
      1 - om * om' * (y / N) ^ 2 :=
  RS9.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_eval_rsEulerPoly N lam om lam' om' hN y hsum

end S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval
end P2MW
export P2MW.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval (solution)
