-- Prove2me | solution 1 for SampleDrivenOS.Limit.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:18:35.702343+00:00
-- url     : https://prove2.me/submissions/adf2f5a8-4d9a-4edb-99d5-b9bbdf9c8145

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting
import Theorems.Thm_SampleDrivenOS_Limit_b4_binomial_identity

open MeasureTheory Filter Topology Set

namespace L4Aux

open SampleDrivenOS.Limit SampleDrivenOS.Structure

/-- pointwise inequality behind Lemma 4 for a nonnegative `q` nonincreasing in `ℓ` -/
lemma pointwise (q : ℝ → ℕ → ℝ) (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hnn : ∀ ℓ, 1 ≤ ℓ → 0 ≤ q x ℓ) (hmono : ∀ ℓ, 1 ≤ ℓ → q x (ℓ + 1) ≤ q x ℓ) :
    ∑ j ∈ Finset.Icc 1 k, x * q x j ≤ ∑ ℓ ∈ Finset.Icc 1 k, q x ℓ * nbTerm k ℓ x := by
  have hanti : ∀ ℓ j, 1 ≤ ℓ → ℓ ≤ j → q x j ≤ q x ℓ := by
    intro ℓ j hℓ hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact le_trans (hmono n (le_trans hℓ hn)) ih
  unfold nbTerm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 k) (s' := fun j => Finset.Icc 1 j)]
  · apply Finset.sum_le_sum
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hb4 := b4_binomial_identity j hj1 x ⟨hx0, hx1⟩
    calc x * q x j = q x j *
          ∑ ℓ ∈ Finset.Icc 1 j, ((j - 1).choose (ℓ - 1) : ℝ) * (1 - x) ^ (j - ℓ) * x ^ ℓ := by
          rw [hb4]; ring
      _ = ∑ ℓ ∈ Finset.Icc 1 j, q x j *
          (((j - 1).choose (ℓ - 1) : ℝ) * (1 - x) ^ (j - ℓ) * x ^ ℓ) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.1 hℓ).1
          have hℓj : ℓ ≤ j := (Finset.mem_Icc.1 hℓ).2
          have hc : 0 ≤ ((j - 1).choose (ℓ - 1) : ℝ) * (1 - x) ^ (j - ℓ) * x ^ ℓ := by
            have : 0 ≤ 1 - x := by linarith
            positivity
          exact mul_le_mul_of_nonneg_right (hanti ℓ j hℓ1 hℓj) hc
  · intro ℓ j
    simp only [Finset.mem_Icc]
    omega

end L4Aux

open L4Aux SampleDrivenOS.Limit SampleDrivenOS.Structure in
theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (q : ℝ → ℕ → ℝ) (α : ℝ)
    (hfeas : SampleDrivenOS.Limit.IsSDFeasible p q α)
    (hmono : ∀ t ∈ Set.Icc p 1, ∀ ℓ : ℕ, 1 ≤ ℓ → q t (ℓ + 1) ≤ q t ℓ)
    (hmax : ∀ c : ℝ, α < c → ¬ SampleDrivenOS.Limit.IsSDFeasible p q c) :
    (⨅ k : {k : ℕ // 1 ≤ k}, 1 / (1 - p ^ (k : ℕ)) *
        ∑ j ∈ Finset.Icc 1 (k : ℕ), ∫ t in p..1, t * q t j) ≤ α := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨⟨hnn, hint, hcon⟩, hα0, hα1, hαk⟩ := hfeas
  have hpk : ∀ k : ℕ, 1 ≤ k → 0 < 1 - p ^ k := by
    intro k hk
    have : p ^ k < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    linarith
  -- integrability
  have hiq : ∀ ℓ, 1 ≤ ℓ → IntervalIntegrable (fun x => x * q x ℓ) volume p 1 := by
    intro ℓ hℓ
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hp1.le]
    exact IntegrableOn.continuousOn_mul continuousOn_id (hint ℓ hℓ) isCompact_Icc
  have hiF : ∀ k ℓ, 1 ≤ ℓ → IntervalIntegrable (fun x => q x ℓ * nbTerm k ℓ x) volume p 1 := by
    intro k ℓ hℓ
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hp1.le]
    apply IntegrableOn.mul_continuousOn (hint ℓ hℓ) _ isCompact_Icc
    unfold nbTerm
    fun_prop
  -- Σ_j ∫ t q(t,j) ≤ F_k, and Σ_j ∫ t q(t,j) ≥ 0
  have hSF : ∀ k : ℕ, ∑ j ∈ Finset.Icc 1 k, ∫ t in p..1, t * q t j ≤ Fk p q k := by
    intro k
    unfold Fk
    rw [← intervalIntegral.integral_finsetSum
        (fun j hj => hiq j (Finset.mem_Icc.1 hj).1),
      ← intervalIntegral.integral_finsetSum (fun ℓ hℓ => hiF k ℓ (Finset.mem_Icc.1 hℓ).1)]
    apply intervalIntegral.integral_mono_on hp1.le
    · have h := IntervalIntegrable.sum (Finset.Icc 1 k)
        (fun j hj => hiq j (Finset.mem_Icc.1 hj).1)
      rw [Finset.sum_fn] at h
      exact h
    · have h := IntervalIntegrable.sum (Finset.Icc 1 k)
        (fun ℓ hℓ => hiF k ℓ (Finset.mem_Icc.1 hℓ).1)
      rw [Finset.sum_fn] at h
      exact h
    · intro x hx
      exact pointwise q k (le_trans hp0.le hx.1) hx.2 (fun ℓ hℓ => hnn x hx ℓ hℓ)
        (fun ℓ hℓ => hmono x hx ℓ hℓ)
  have hS0 : ∀ k : ℕ, 0 ≤ ∑ j ∈ Finset.Icc 1 k, ∫ t in p..1, t * q t j := by
    intro k
    apply Finset.sum_nonneg
    intro j hj
    apply intervalIntegral.integral_nonneg hp1.le
    intro x hx
    exact mul_nonneg (le_trans hp0.le hx.1) (hnn x hx j (Finset.mem_Icc.1 hj).1)
  -- the value at k = 1 is at most 1
  have hk1 : 1 / (1 - p ^ 1) * ∑ j ∈ Finset.Icc 1 1, ∫ t in p..1, t * q t j ≤ 1 := by
    simp only [pow_one, Finset.Icc_self, Finset.sum_singleton]
    rw [one_div_mul_eq_div, div_le_one (by linarith)]
    have : ∫ t in p..1, t * q t 1 ≤ ∫ t in p..1, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on hp1.le (hiq 1 le_rfl) intervalIntegrable_const
      intro x hx
      have h := hcon x hx 1 le_rfl
      have h1 : ENNReal.ofReal (x * q x 1) ≤ 1 := le_trans le_self_add h
      have h2 := (ENNReal.ofReal_le_one).1 h1
      exact h2
    simpa using this
  set f : {k : ℕ // 1 ≤ k} → ℝ := fun k => 1 / (1 - p ^ (k : ℕ)) *
      ∑ j ∈ Finset.Icc 1 (k : ℕ), ∫ t in p..1, t * q t j
  have hfnn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (by have := hpk k.1 k.2; positivity) (hS0 k.1)
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hfnn k⟩
  by_contra hlt
  push Not at hlt
  -- α < f k for all k, and f ≤ F_k/(1-p^k)
  have hlt' : ∀ k : {k : ℕ // 1 ≤ k}, α < f k := fun k =>
    lt_of_lt_of_le hlt (ciInf_le hbdd k)
  have hαlt1 : α < 1 := lt_of_lt_of_le (hlt' ⟨1, le_rfl⟩) hk1
  set c := min 1 (⨅ k : {k : ℕ // 1 ≤ k}, f k)
  have hc : α < c := lt_min hαlt1 hlt
  apply hmax c hc
  refine ⟨⟨hnn, hint, hcon⟩, le_trans hα0 hc.le, min_le_left _ _, ?_⟩
  intro k hk
  have h1 : c ≤ f ⟨k, hk⟩ := le_trans (min_le_right _ _)
    (ciInf_le hbdd ⟨k, hk⟩)
  refine le_trans h1 ?_
  simp only [f]
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (hSF k) (hpk k hk).le
