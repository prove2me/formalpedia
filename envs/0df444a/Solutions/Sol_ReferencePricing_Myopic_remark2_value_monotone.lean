-- Prove2me | solution 1 for ReferencePricing.Myopic.remark2_value_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:10:08.851954+00:00
-- url     : https://prove2.me/submissions/d9cecfd0-44f1-4684-9faa-0b6e1f79c693

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_value

open ReferencePricing.Myopic in
theorem solution (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hR0 : ∀ r, R 0 r = 0) (hA1 : Assumption1 d R pbar) :
    MonotoneOn (value (profit d R) α β pbar) (Set.Icc 0 pbar) := by
  obtain ⟨M, hM⟩ := hA1.demand_bounded
  have hpath : ∀ r ∈ Set.Icc (0 : ℝ) pbar, ∀ p : ℕ → Set.Icc (0 : ℝ) pbar, ∀ t,
      refPath α r (fun s => (p s : ℝ)) t ∈ Set.Icc (0 : ℝ) pbar := by
    intro r hr p t
    induction t with
    | zero => exact hr
    | succ t ih =>
      simp only [refPath]
      have hp := (p t).2
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := hp
      constructor
      · nlinarith
      · nlinarith
  have hprof_nn : ∀ q ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar, 0 ≤ profit d R q r :=
    fun q hq r hr => mul_nonneg hq.1 (hA1.demand_nonneg q hq r hr)
  have hprof_le : ∀ q ∈ Set.Icc (0 : ℝ) pbar, ∀ r ∈ Set.Icc (0 : ℝ) pbar,
      profit d R q r ≤ pbar * M := by
    intro q hq r hr
    unfold profit
    have h0 := hA1.demand_nonneg q hq r hr
    have h1 := hM q hq r hr
    exact mul_le_mul hq.2 h1 h0 hpbar.le
  have hgeo := summable_geometric_of_lt_one hβ₀.le hβ₁
  have hsum : ∀ r ∈ Set.Icc (0 : ℝ) pbar, ∀ p : ℕ → Set.Icc (0 : ℝ) pbar,
      Summable (fun t => β ^ t * profit d R (p t) (refPath α r (fun s => (p s : ℝ)) t)) := by
    intro r hr p
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ₀.le t)
      (hprof_nn _ (p t).2 _ (hpath r hr p t))) (fun t => mul_le_mul_of_nonneg_left
      (hprof_le _ (p t).2 _ (hpath r hr p t)) (pow_nonneg hβ₀.le t)) (hgeo.mul_right (pbar * M))
  have hbdd : ∀ r ∈ Set.Icc (0 : ℝ) pbar, ∀ p : ℕ → Set.Icc (0 : ℝ) pbar,
      ∑' t, β ^ t * profit d R (p t) (refPath α r (fun s => (p s : ℝ)) t) ≤
        ∑' t : ℕ, β ^ t * (pbar * M) := by
    intro r hr p
    exact (hsum r hr p).tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left
      (hprof_le _ (p t).2 _ (hpath r hr p t)) (pow_nonneg hβ₀.le t)) (hgeo.mul_right (pbar * M))
  intro r0 hr0 r0' hr0' hle
  have hmono : ∀ p : ℕ → Set.Icc (0 : ℝ) pbar, ∀ t,
      refPath α r0 (fun s => (p s : ℝ)) t ≤ refPath α r0' (fun s => (p s : ℝ)) t := by
    intro p t
    induction t with
    | zero => exact hle
    | succ t ih =>
      simp only [refPath]
      have := mul_le_mul_of_nonneg_left ih hα₀
      linarith
  unfold value
  apply ciSup_mono
  · refine ⟨∑' t : ℕ, β ^ t * (pbar * M), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hbdd r0' hr0' p
  · intro p
    refine (hsum r0 hr0 p).tsum_le_tsum (fun t => ?_) (hsum r0' hr0' p)
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ₀.le t)
    unfold profit
    refine mul_le_mul_of_nonneg_left ?_ (p t).2.1
    exact hA1.demand_monotone_ref _ (p t).2 (hpath r0 hr0 p t) (hpath r0' hr0' p t) (hmono p t)
