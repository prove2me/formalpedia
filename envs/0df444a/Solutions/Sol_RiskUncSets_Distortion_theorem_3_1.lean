-- Prove2me | solution 1 for RiskUncSets.Distortion.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:04:04.094015+00:00
-- url     : https://prove2.me/submissions/014c4db2-92ee-4498-af1f-d0eb5b39054e

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

open RiskUncSets.Distortion Finset MeasureTheory



theorem ru83_gen_le {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ} (h : Generates Q μ)
    (X : Fin N → ℝ) {q : Fin N → ℝ} (hq : q ∈ Q) : ∑ i, q i * (-X i) ≤ μ X :=
  (h.2 X).1 ⟨q, hq, rfl⟩

theorem ru83_gen_ub {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ} (h : Generates Q μ)
    (X : Fin N → ℝ) (c : ℝ) (hc : ∀ q ∈ Q, ∑ i, q i * (-X i) ≤ c) : μ X ≤ c :=
  (h.2 X).2 (by rintro _ ⟨q, hq, rfl⟩; exact hc q hq)

theorem ru83_gen_nonempty {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ}
    (h : Generates Q μ) : Q.Nonempty := by
  by_contra hQ
  rw [Set.not_nonempty_iff_eq_empty] at hQ
  have := ru83_gen_ub h 0 (μ 0 - 1) (by simp [hQ])
  linarith

theorem ru83_gen_coherent {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ}
    (h : Generates Q μ) : IsCoherent μ := by
  obtain ⟨q0, hq0⟩ := ru83_gen_nonempty h
  have hsum : ∀ q ∈ Q, ∑ i, q i = 1 := fun q hq => (h.1 hq).2
  have hnn : ∀ q ∈ Q, ∀ i, 0 ≤ q i := fun q hq => (h.1 hq).1
  refine ⟨⟨fun X Y hXY => ?_, fun X c => ?_⟩, fun X Y t ht0 ht1 => ?_, fun X t ht => ?_⟩
  · refine ru83_gen_ub h X _ fun q hq => le_trans ?_ (ru83_gen_le h Y hq)
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hXY i]) (hnn q hq i)
  · have hv : ∀ q ∈ Q, ∑ i, q i * (-(X i + c)) = ∑ i, q i * (-X i) - c := fun q hq => by
      simp only [neg_add, mul_add, sum_add_distrib, ← sum_mul, hsum q hq]; ring
    apply le_antisymm
    · refine ru83_gen_ub h _ _ fun q hq => ?_
      rw [hv q hq]; linarith [ru83_gen_le h X hq]
    · have : μ X ≤ μ (fun i => X i + c) + c := ru83_gen_ub h X _ fun q hq => by
        have := ru83_gen_le h (fun i => X i + c) hq
        rw [hv q hq] at this; linarith
      linarith
  · refine ru83_gen_ub h _ _ fun q hq => ?_
    have e : ∑ i, q i * (-(t • X + (1 - t) • Y) i) =
        t * ∑ i, q i * (-X i) + (1 - t) * ∑ i, q i * (-Y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 := ru83_gen_le h X hq
    have h2 := ru83_gen_le h Y hq
    nlinarith
  · have e : ∀ q : Fin N → ℝ, ∑ i, q i * (-(t • X) i) = t * ∑ i, q i * (-X i) := fun q => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun i _ => by ring
    rcases ht.eq_or_lt with rfl | htp
    · simp only [zero_mul]
      apply le_antisymm
      · exact ru83_gen_ub h _ _ fun q hq => by rw [e]; simp
      · have := ru83_gen_le h ((0:ℝ) • X) hq0; rw [e] at this; simpa using this
    · apply le_antisymm
      · exact ru83_gen_ub h _ _ fun q hq => by
          rw [e]; exact mul_le_mul_of_nonneg_left (ru83_gen_le h X hq) ht
      · have : μ X ≤ (1 / t) * μ (t • X) := ru83_gen_ub h X _ fun q hq => by
          have := ru83_gen_le h (t • X) hq
          rw [e] at this
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ htp]; linarith
        have h2 := mul_le_mul_of_nonneg_left this ht
        rw [← mul_assoc, mul_one_div_cancel htp.ne', one_mul] at h2
        exact h2



theorem ru83_val {N n : ℕ} (a : Fin N → Fin n → ℝ) (b : ℝ) (x : Fin n → ℝ) (q : Fin N → ℝ)
    (hq : ∑ i, q i = 1) :
    ∑ i, q i * (-(fun i => a i ⬝ᵥ x - b) i) = b - (∑ i, q i • a i) ⬝ᵥ x := by
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, mul_neg, mul_sub, sum_neg_distrib, sum_sub_distrib,
    ← sum_mul, hq]
  ring

theorem ru83_halfspace_convex {n : ℕ} (b : ℝ) (x : Fin n → ℝ) :
    Convex ℝ {a' : Fin n → ℝ | b ≤ a' ⬝ᵥ x} := by
  intro y hy z hz s t hs ht hst
  simp only [Set.mem_setOf_eq, add_dotProduct, smul_dotProduct, smul_eq_mul] at *
  have e : b = s * b + t * b := by rw [← add_mul, hst, one_mul]
  linarith [mul_le_mul_of_nonneg_left hy hs, mul_le_mul_of_nonneg_left hz ht]

theorem ru83_hull_sub {N n : ℕ} (a : Fin N → Fin n → ℝ) :
    convexHull ℝ (Set.range a) ⊆
      (fun q : Fin N → ℝ => ∑ i, q i • a i) '' stdSimplex ℝ (Fin N) := by
  refine convexHull_min ?_ ?_
  · rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ⟨fun i => ?_, by simp⟩, by simp [Pi.single_apply]⟩
    by_cases h : i = j <;> simp [Pi.single_apply, h]
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩ s t hs ht hst
    refine ⟨s • q + t • r, convex_stdSimplex ℝ (Fin N) hq hr hs ht hst, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, sum_add_distrib, mul_smul,
      ← smul_sum]

theorem ru83_thm31 {N : ℕ} {n : ℕ} (a : Fin N → Fin n → ℝ) (b : ℝ) :
    (∀ (μ : (Fin N → ℝ) → ℝ) (Q : Set (Fin N → ℝ)), IsCoherent μ → Generates Q μ →
        {x : Fin n → ℝ | μ (fun i => a i ⬝ᵥ x - b) ≤ 0} =
          {x | ∀ a' ∈ convexHull ℝ ((fun q : Fin N → ℝ => ∑ i, q i • a i) '' Q),
            b ≤ a' ⬝ᵥ x}) ∧
      (∀ U : Set (Fin n → ℝ), U.Nonempty → U ⊆ convexHull ℝ (Set.range a) →
        (∃ μ : (Fin N → ℝ) → ℝ,
          Generates {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∃ a' ∈ U, ∑ i, q i • a i = a'} μ) ∧
        ∀ μ : (Fin N → ℝ) → ℝ,
          Generates {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∃ a' ∈ U, ∑ i, q i • a i = a'} μ →
            IsCoherent μ ∧
              {x : Fin n → ℝ | μ (fun i => a i ⬝ᵥ x - b) ≤ 0} = {x | ∀ a' ∈ U, b ≤ a' ⬝ᵥ x}) := by
  refine ⟨fun μ Q _ hG => ?_, fun U hU hUa => ⟨?_, fun μ hG => ⟨ru83_gen_coherent hG, ?_⟩⟩⟩
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      have hsub : (fun q : Fin N → ℝ => ∑ i, q i • a i) '' Q ⊆ {a' | b ≤ a' ⬝ᵥ x} := by
        rintro _ ⟨q, hq, rfl⟩
        have := ru83_gen_le hG (fun i => a i ⬝ᵥ x - b) hq
        rw [ru83_val a b x q (hG.1 hq).2] at this
        simp only [Set.mem_setOf_eq]; linarith
      exact fun a' ha' => convexHull_min hsub (ru83_halfspace_convex b x) ha'
    · intro hx
      refine ru83_gen_ub hG _ _ fun q hq => ?_
      rw [ru83_val a b x q (hG.1 hq).2]
      have := hx _ (subset_convexHull ℝ _ ⟨q, hq, rfl⟩)
      linarith
  · set Q := {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∃ a' ∈ U, ∑ i, q i • a i = a'}
    refine ⟨fun X => sSup ((fun q : Fin N → ℝ => ∑ i, q i * (-X i)) '' Q), fun q hq => hq.1,
      fun X => isLUB_csSup ?_ ?_⟩
    · obtain ⟨a', ha'⟩ := hU
      obtain ⟨q, hq, hqa⟩ := ru83_hull_sub a (hUa ha')
      exact ⟨_, q, ⟨hq, a', ha', hqa⟩, rfl⟩
    · refine ⟨∑ i, |X i|, ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      refine sum_le_sum fun i _ => ?_
      have h0 := hq.1.1 i
      have h1 : q i ≤ 1 := by
        rw [← hq.1.2]; exact single_le_sum (fun j _ => hq.1.1 j) (mem_univ i)
      have := neg_le_abs (X i)
      have : q i * (-X i) ≤ q i * |X i| := mul_le_mul_of_nonneg_left this h0
      nlinarith [abs_nonneg (X i)]
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx a' ha'
      obtain ⟨q, hq, hqa⟩ := ru83_hull_sub a (hUa ha')
      simp only at hqa
      have := ru83_gen_le hG (fun i => a i ⬝ᵥ x - b) (q := q) ⟨hq, a', ha', hqa⟩
      rw [ru83_val a b x q hq.2, hqa] at this
      linarith
    · intro hx
      refine ru83_gen_ub hG _ _ fun q hq => ?_
      obtain ⟨hqs, a', ha', hqa⟩ := hq
      rw [ru83_val a b x q hqs.2, hqa]
      linarith [hx a' ha']


theorem solution {N : ℕ} (hN : 0 < N) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) {n : ℕ} (a : Fin N → Fin n → ℝ) (b : ℝ) :
    (∀ (μ : (Fin N → ℝ) → ℝ) (Q : Set (Fin N → ℝ)), IsCoherent μ → Generates Q μ →
        (∀ q ∈ Q, ∀ i, p i = 0 → q i = 0) →
        {x : Fin n → ℝ | μ (fun i => a i ⬝ᵥ x - b) ≤ 0} =
          {x | ∀ a' ∈ convexHull ℝ ((fun q : Fin N → ℝ => ∑ i, q i • a i) '' Q),
            b ≤ a' ⬝ᵥ x}) ∧
      (∀ U : Set (Fin n → ℝ), U.Nonempty → U ⊆ convexHull ℝ (Set.range a) →
        (∃ μ : (Fin N → ℝ) → ℝ,
          Generates {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∃ a' ∈ U, ∑ i, q i • a i = a'} μ) ∧
        ∀ μ : (Fin N → ℝ) → ℝ,
          Generates {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∃ a' ∈ U, ∑ i, q i • a i = a'} μ →
            IsCoherent μ ∧
              {x : Fin n → ℝ | μ (fun i => a i ⬝ᵥ x - b) ≤ 0} = {x | ∀ a' ∈ U, b ≤ a' ⬝ᵥ x}) := by


  obtain ⟨h1, h2⟩ := ru83_thm31 a b
  exact ⟨fun μ Q hc hG _ => h1 μ Q hc hG, h2⟩
