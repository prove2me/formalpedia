-- Prove2me | solution 1 for PrimalDualSubgrad.DA.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:12:36.393195+00:00
-- url     : https://prove2.me/submissions/5b809228-4ff9-4282-9ea0-f23860699472

import Mathlib
open Set Metric

private theorem growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ} {σ : ℝ} (hsc : StrongConvexOn Q σ d)
    {xs x : E} (hs : xs ∈ Q) (hx : x ∈ Q)
    (hm : ∀ y ∈ Q, d xs ≤ d y) :
    d xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ d x := by
  have hb : 0 ≤ d x - d xs := sub_nonneg.mpr (hm x hx)
  by_contra h
  let A := σ / 2 * ‖x - xs‖ ^ 2
  let B := d x - d xs
  have hBA : B < A := by dsimp [A, B]; linarith
  have hB : 0 ≤ B := hb
  have hA : 0 < A := lt_of_le_of_lt hB hBA
  let t := (A - B) / (2 * A)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hteq : t * (2 * A) = A - B := by dsimp [t]; field_simp
  have hc := hsc.2 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmem := hsc.1 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmin := hm _ hmem
  simp only [smul_eq_mul, norm_sub_rev xs x] at hc
  have hc' : 0 ≤ t * (B - (1 - t) * A) := by dsimp [A, B]; nlinarith [hc]
  have hb' : (1 - t) * A ≤ B := by nlinarith
  nlinarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : Set E) (d : E → ℝ) (σ : ℝ)
    (hQc : IsClosed Q) (hQconv : Convex ℝ Q) (hQne : Q.Nonempty)
    (hd : ContinuousOn d Q) (hσ : 0 < σ) (hsc : StrongConvexOn Q σ d) :
    (∃! xs : E, xs ∈ Q ∧ ∀ x ∈ Q, d xs ≤ d x) ∧
      ∀ xs ∈ Q, (∀ x ∈ Q, d xs ≤ d x) → ∀ x ∈ Q, d xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ d x := by
  obtain ⟨x0, hx0⟩ := hQne
  have hK : IsCompact (Q ∩ closedBall x0 1) := (isCompact_closedBall x0 1).inter_left hQc
  have hKne : (Q ∩ closedBall x0 1).Nonempty := ⟨x0, hx0, by simp⟩
  obtain ⟨y, hy, hmy⟩ := hK.exists_isMinOn hKne (hd.mono inter_subset_left)
  let k := σ / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hL : d y ≤ d x0 := hmy (show x0 ∈ Q ∩ closedBall x0 1 from ⟨hx0, by simp⟩)
  let R := 2 + (d x0 - d y) / k
  have hR : 2 ≤ R := by dsimp [R]; have := div_nonneg (sub_nonneg.mpr hL) hk.le; linarith
  have outside (x : E) (hx : x ∈ Q) (hr : R < ‖x - x0‖) : d x0 ≤ d x := by
    let r := ‖x - x0‖
    have hr1 : 1 < r := by dsimp [r]; linarith
    have hrpos : 0 < r := by linarith
    let t := 1 / r
    have ht : 0 < t := by dsimp [t]; positivity
    have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ hrpos).mpr; linarith
    let z := (1 - t) • x0 + t • x
    have hzQ : z ∈ Q := hQconv hx0 hx (sub_nonneg.mpr ht1) ht.le (by ring)
    have hv : z - x0 = t • (x - x0) := by dsimp [z]; module
    have hzball : z ∈ closedBall x0 1 := by
      rw [mem_closedBall, dist_eq_norm, hv, norm_smul, Real.norm_of_nonneg ht.le]
      change t * r ≤ 1
      dsimp [t]
      rw [one_div_mul_cancel hrpos.ne']
    have hlower : d y ≤ d z := hmy ⟨hzQ, hzball⟩
    have hc := hsc.2 hx0 hx (sub_nonneg.mpr ht1) ht.le (by ring : 1-t+t=1)
    have he : (1-t)*t*(σ/2*‖x0-x‖^2) = k*(r-1) := by
      rw [norm_sub_rev]
      change (1 - 1/r)*(1/r)*(k*r^2) = k*(r-1)
      field_simp [hrpos.ne']
      <;> ring
    simp only [smul_eq_mul, he] at hc
    change d z ≤ (1-t)*d x0+t*d x-k*(r-1) at hc
    have hRk : R * k = 2 * k + d x0 - d y := by dsimp [R]; field_simp [hk.ne']; ring
    have hrk : R * k < r * k := mul_lt_mul_of_pos_right hr hk
    by_contra hn
    have hneg : t * (d x - d x0) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
    nlinarith
  have hBig : IsCompact (Q ∩ closedBall x0 R) := (isCompact_closedBall x0 R).inter_left hQc
  obtain ⟨xs, hxs, hmxs⟩ := hBig.exists_isMinOn
    (show (Q ∩ closedBall x0 R).Nonempty from ⟨x0, hx0, by simp; linarith⟩)
    (hd.mono inter_subset_left)
  have hmglobal : ∀ x ∈ Q, d xs ≤ d x := by
    intro x hx
    by_cases hb : ‖x - x0‖ ≤ R
    · exact hmxs ⟨hx, by rwa [mem_closedBall, dist_eq_norm]⟩
    · have h0 := hmxs (show x0 ∈ Q ∩ closedBall x0 R from ⟨hx0, by simp; linarith⟩)
      exact h0.trans (outside x hx (lt_of_not_ge hb))
  constructor
  · refine ⟨xs, ⟨hxs.1, hmglobal⟩, ?_⟩
    intro z hz
    exact (hsc.strictConvexOn hσ).eq_of_isMinOn hz.2 hmglobal hz.1 hxs.1
  · intro z hz hm x hx
    exact growth hsc hz hx hm

#print axioms solution
