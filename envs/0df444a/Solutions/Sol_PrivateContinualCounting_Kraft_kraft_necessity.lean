-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.kraft_necessity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:44:59.673608+00:00
-- url     : https://prove2.me/submissions/2583af49-75bf-431a-8fb3-c572edb2f58b

import Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_kraft_blocks
import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes

set_option autoImplicit false

open Finset Filter Topology

namespace PCCKraftNec
open PrivateContinualCounting.Kraft

lemma vectorSq_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ vectorSq x :=
  sum_nonneg (fun q _ => sq_nonneg _)

lemma abs_dot_le {m : ℕ} (x y : Fin m → ℝ) :
    |∑ q, x q * y q| ≤ Real.sqrt (vectorSq x) * Real.sqrt (vectorSq y) := by
  have hcs := sum_mul_sq_le_sq_mul_sq univ x y
  have hx : vectorSq x = ∑ q, x q ^ 2 := by simp [vectorSq, Real.norm_eq_abs, sq_abs]
  have hy : vectorSq y = ∑ q, y q ^ 2 := by simp [vectorSq, Real.norm_eq_abs, sq_abs]
  rw [hx, hy, ← Real.sqrt_mul (sum_nonneg (fun q _ => sq_nonneg _))]
  exact Real.abs_le_sqrt hcs

/-- The norm data of real vector LTI factors satisfy the hypotheses of the core lemmas. -/
lemma lti_norms {m : ℕ} (d : LTIData ℝ m) (hd : IsLTI d) :
    (∀ j, 0 ≤ Real.sqrt (vectorSq (d.l j))) ∧ (∀ k, 0 ≤ Real.sqrt (vectorSq (d.r k))) ∧
    Summable (fun k => Real.sqrt (vectorSq (d.r k)) ^ 2) ∧
    (∀ s, 1 ≤ ∑ j ∈ range (s + 1),
      Real.sqrt (vectorSq (d.l j)) * Real.sqrt (vectorSq (d.r (s - j)))) ∧
    (∀ t, ∑ j ∈ range t, Real.sqrt (vectorSq (d.l j)) ^ 2 = d.energy t) ∧
    (∀ k, Real.sqrt (vectorSq (d.r k)) ^ 2 = vectorSq (d.r k)) := by
  obtain ⟨_, hconv, hsum⟩ := hd
  have hsq : ∀ x : Fin m → ℝ, Real.sqrt (vectorSq x) ^ 2 = vectorSq x :=
    fun x => Real.sq_sqrt (vectorSq_nonneg x)
  refine ⟨fun j => Real.sqrt_nonneg _, fun k => Real.sqrt_nonneg _, ?_, ?_, ?_, fun k => hsq _⟩
  · simpa [hsq] using hsum
  · intro s
    calc (1:ℝ) = ∑ j ∈ range (s + 1), ∑ q, d.l j q * d.r (s - j) q := (hconv s).symm
      _ ≤ ∑ j ∈ range (s + 1), |∑ q, d.l j q * d.r (s - j) q| :=
          sum_le_sum (fun j _ => le_abs_self _)
      _ ≤ _ := sum_le_sum (fun j _ => abs_dot_le _ _)
  · intro t; simp [LTIData.energy, hsq]

lemma deltaSq_pos {m : ℕ} (d : LTIData ℝ m) (hd : IsLTI d) : 0 < d.deltaSq := by
  obtain ⟨hα, hβ, hβ2, hid, _, hsq⟩ := lti_norms d hd
  have h0 := hid 0
  simp only [zero_add, sum_range_one, Nat.sub_zero] at h0
  have hb : 0 < Real.sqrt (vectorSq (d.r 0)) := by
    by_contra h
    have : Real.sqrt (vectorSq (d.r 0)) = 0 := le_antisymm (not_lt.mp h) (hβ 0)
    rw [this, mul_zero] at h0
    linarith
  have hv : 0 < vectorSq (d.r 0) := by rw [← hsq]; positivity
  have hsum : Summable (fun k => vectorSq (d.r k)) := by simpa [hsq] using hβ2
  exact lt_of_lt_of_le hv (hsum.le_tsum 0 (fun k _ => vectorSq_nonneg _))

end PCCKraftNec

open PrivateContinualCounting.Kraft in
theorem solution (m : ℕ) (d : LTIData ℝ m) (hd : IsLTI d) (g : ℝ → ℝ)
    (hg1 : ∀ u : ℝ, 1 ≤ u → 1 ≤ g u) (hgm : MonotoneOn g (Set.Ici 1))
    (henv : HasEnvelope d.variance g) : KraftCondition g := by
  obtain ⟨hα, hβ, hβ2, hid, hE, _⟩ := PCCKraftNec.lti_norms d hd
  obtain ⟨C, hC, hCb⟩ := henv
  have hΔ := PCCKraftNec.deltaSq_pos d hd
  unfold KraftCondition
  refine hilbert_kraft_blocks _ _ hα hβ hβ2 hid g hg1 hgm (C / d.deltaSq) (fun t ht => ?_)
  rw [hE]
  have := hCb t ht
  rw [LTIData.variance] at this
  have e : C / d.deltaSq * Real.log ↑t ^ 2 * g (Real.log ↑t) =
      (C * Real.log ↑t ^ 2 * g (Real.log ↑t)) / d.deltaSq := by ring
  rw [e, le_div_iff₀ hΔ]
  linarith
