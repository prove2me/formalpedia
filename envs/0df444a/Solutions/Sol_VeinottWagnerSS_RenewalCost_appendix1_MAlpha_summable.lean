-- Prove2me | solution 1 for VeinottWagnerSS.RenewalCost.appendix1_MAlpha_summable
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:46:01.779129+00:00
-- url     : https://prove2.me/submissions/f637c836-e4c9-4497-86fc-68c41dacf095

import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
import Mathlib.Tactic

open Filter VeinottWagnerSS.RenewalCost
open scoped Topology

namespace CVeinottRenewal

theorem summable_recurrence (u v : ℕ → ℝ) (q : ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hvs : Summable v) (hrec : ∀ n, u (n + 1) ≤ q * u n + v n) : Summable u := by
  apply summable_of_sum_range_le hu (c := (u 0 + ∑' n, v n) / (1 - q))
  intro N
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hrec n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hshift : (∑ n ∈ Finset.range N, u (n + 1)) + u 0 =
      (∑ n ∈ Finset.range N, u n) + u N := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ]
  have hbound := hvs.sum_le_tsum (Finset.range N) (fun n _ => hv n)
  apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith [hu N]

theorem conv_nonneg (D : DemandDist) (i k : ℕ) : 0 ≤ convPow D.φ i k := by
  induction i generalizing k with
  | zero => simp only [convPow]; split_ifs <;> norm_num
  | succ i hi =>
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (D.nonneg _) (hi j))

theorem weighted_conv_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ i * convPow D.φ i k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let u : ℕ → ℝ := fun i => α ^ i * convPow D.φ i k
    let v : ℕ → ℝ := fun i => ∑ j ∈ Finset.range k,
      (α * D.φ (k - j)) * (α ^ i * convPow D.φ i j)
    have hu : ∀ i, 0 ≤ u i := fun i => mul_nonneg (pow_nonneg hα0 _) (conv_nonneg D _ _)
    have hv : ∀ i, 0 ≤ v i := fun i => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg hα0 (D.nonneg _)) (mul_nonneg (pow_nonneg hα0 _) (conv_nonneg D _ _)))
    have hvs : Summable v := by
      apply summable_sum
      intro j hj
      exact (ih j (Finset.mem_range.mp hj)).mul_left (α * D.φ (k - j))
    apply summable_recurrence u v (α * D.φ 0) hu hv (mul_nonneg hα0 (D.nonneg 0)) hφ0 hvs
    intro i
    have heq : u (i + 1) = (α * D.φ 0) * u i + v i := by
      dsimp [u, v]
      simp only [convPow]
      rw [Finset.sum_range_succ, mul_add, Nat.sub_self]
      simp only [Finset.mul_sum]
      rw [add_comm]
      congr 1
      · rw [pow_succ]; ring
      · apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ]
        ring
    exact heq.le

theorem weighted_cdf_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ i * cdfPow D.φ i k) := by
  simp only [cdfPow, Finset.mul_sum]
  apply summable_sum
  intro j hj
  exact weighted_conv_summable D α hα0 hφ0 j

theorem appendix_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ (i + 1) * cdfPow D.φ (i + 1) k) := by
  exact (weighted_cdf_summable D α hα0 hφ0 k).comp_injective
    (show Function.Injective (fun i : ℕ => i + 1) by intro a b h; exact Nat.add_right_cancel h)

end CVeinottRenewal

namespace CVeinottRenewal

theorem weighted_conv_succ_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ (i + 1) * convPow D.φ (i + 1) k) := by
  exact (weighted_conv_summable D α hα0 hφ0 k).comp_injective
    (show Function.Injective (fun i : ℕ => i + 1) by intro a b h; exact Nat.add_right_cancel h)

theorem LAlpha_interchange (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (G : ℤ → ℝ) (x : ℤ) (d : ℕ) :
    Summable (fun i : ℕ => ∑ k ∈ Finset.range (d + 1),
        |α ^ (i + 1) * G (x - (k : ℤ)) * convPow D.φ (i + 1) k|) ∧
      LAlpha D.φ α G x d =
        G x + ∑ j ∈ Finset.range (d + 1), G (x - (j : ℤ)) * mAlpha D.φ α j := by
  have hterm : ∀ k : ℕ, Summable (fun i : ℕ =>
      α ^ (i + 1) * G (x - (k : ℤ)) * convPow D.φ (i + 1) k) := by
    intro k
    convert! (weighted_conv_succ_summable D α hα0 hφ0 k).mul_left (G (x - (k : ℤ))) using 1
    congr 1
    funext i
    ring
  constructor
  · apply summable_sum
    intro k hk
    exact (hterm k).abs
  · unfold LAlpha
    rw [Summable.tsum_finsetSum (fun k _ => hterm k)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    unfold mAlpha
    rw [← (weighted_conv_succ_summable D α hα0 hφ0 k).tsum_mul_left]
    apply tsum_congr
    intro i
    ring

theorem rAlpha_closed_form (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α)
    (hφ0 : α * D.φ 0 < 1) (d : ℕ) :
    rAlpha D.φ α d = α - (1 - α) * MAlpha D.φ α d := by
  have hs := weighted_cdf_summable D α hα0 hφ0 d
  have hs' := appendix_summable D α hα0 hφ0 d
  have hfirst : Summable (fun i : ℕ => α ^ (i + 1) * cdfPow D.φ i d) := by
    simpa only [pow_succ', mul_assoc] using hs.mul_left α
  have hzero : cdfPow D.φ 0 d = 1 := by
    simp [cdfPow, convPow]
  have htotal : (∑' i : ℕ, α ^ i * cdfPow D.φ i d) = 1 + MAlpha D.φ α d := by
    rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, hzero, MAlpha]
  have hfirst_eq : (∑' i : ℕ, α ^ (i + 1) * cdfPow D.φ i d) =
      α * (1 + MAlpha D.φ α d) := by
    simp_rw [pow_succ', mul_assoc]
    rw [hs.tsum_mul_left, htotal]
  unfold rAlpha
  simp only [mul_sub]
  rw [hfirst.tsum_sub hs', hfirst_eq]
  change α * (1 + MAlpha D.φ α d) - MAlpha D.φ α d = _
  ring

end CVeinottRenewal

theorem solution (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ (i + 1) * cdfPow D.φ (i + 1) k) := by
  exact CVeinottRenewal.appendix_summable D α hα0 hφ0 k
