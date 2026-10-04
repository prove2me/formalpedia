-- Prove2me | solution 1 for SennottDP.FiniteHorizon.weighted_sum_ge_min
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:05:52.360825+00:00
-- url     : https://prove2.me/submissions/011ca9e7-9d59-487a-a7fc-6f4706c856b0

import Mathlib

set_option autoImplicit false

lemma b5246f2d_coe_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) :
    ((∑ a ∈ s, c a : ℝ) : EReal) = ∑ a ∈ s, (c a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, EReal.coe_add, ih]

lemma b5246f2d_sum_top {ι : Type} (s : Finset ι) (t : ι → EReal) (c : ι → ℝ)
    (hc : ∀ a ∈ s, (c a : EReal) ≤ t a) (a0 : ι) (h0 : a0 ∈ s) (ht : t a0 = ⊤) :
    ∑ a ∈ s, t a = ⊤ := by
  classical
  rw [← Finset.add_sum_erase s t h0, ht]
  apply EReal.top_add_of_ne_bot
  have h : ((∑ a ∈ s.erase a0, c a : ℝ) : EReal) ≤ ∑ a ∈ s.erase a0, t a := by
    rw [b5246f2d_coe_sum]
    exact Finset.sum_le_sum (fun a ha => hc a (Finset.mem_of_mem_erase ha))
  intro hb
  rw [hb] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h)

theorem solution {ι : Type} (A : Finset ι) (hA : A.Nonempty) (q : ι → ℝ)
    (hq_nonneg : ∀ a ∈ A, 0 ≤ q a) (hq_sum : ∑ a ∈ A, q a = 1)
    (u : ι → EReal) (hu : ∀ a ∈ A, u a ≠ ⊥) :
    A.inf' hA u ≤ ∑ a ∈ A, ((q a : ℝ) : EReal) * u a ∧
    (∑ a ∈ A, ((q a : ℝ) : EReal) * u a = A.inf' hA u ↔
      ∀ a ∈ A, u a ≠ A.inf' hA u → q a = 0) := by
  classical
  have hle : ∀ a ∈ A, A.inf' hA u ≤ u a := fun a ha => Finset.inf'_le u ha
  -- some index carries positive weight
  have hpos : ∃ a ∈ A, 0 < q a := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have : ∑ a ∈ A, q a ≤ 0 := Finset.sum_nonpos h
    linarith
  obtain ⟨a1, ha1, hq1⟩ := hpos
  obtain ⟨a2, ha2, hm2⟩ := Finset.exists_mem_eq_inf' hA u
  generalize A.inf' hA u = m at hle hm2 ⊢
  induction m using EReal.rec with
  | bot => exact absurd hm2.symm (hu a2 ha2)
  | top =>
    have hall : ∀ a ∈ A, u a = ⊤ := fun a ha => top_le_iff.mp (hle a ha)
    have hsum : ∑ a ∈ A, ((q a : ℝ) : EReal) * u a = ⊤ := by
      apply b5246f2d_sum_top A _ (fun _ => 0) _ a1 ha1
      · rw [hall a1 ha1]; exact EReal.coe_mul_top_of_pos hq1
      · intro a ha
        rw [hall a ha]
        rcases (hq_nonneg a ha).lt_or_eq with h | h
        · rw [EReal.coe_mul_top_of_pos h]; exact le_top
        · rw [← h]; simp
    refine ⟨by rw [hsum], ?_⟩
    constructor
    · intro _ a ha hne; exact absurd (hall a ha) hne
    · intro _; exact hsum
  | coe r =>
    -- termwise lower bound
    have hlow : ∀ a ∈ A, ((q a * r : ℝ) : EReal) ≤ ((q a : ℝ) : EReal) * u a := by
      intro a ha
      have h1 := hle a ha
      induction hua : u a using EReal.rec with
      | bot => exact absurd hua (hu a ha)
      | top =>
        rcases (hq_nonneg a ha).lt_or_eq with h | h
        · rw [EReal.coe_mul_top_of_pos h]; exact le_top
        · rw [← h]; simp
      | coe v =>
        rw [hua] at h1
        rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
        exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h1) (hq_nonneg a ha)
    have hrsum : ((∑ a ∈ A, q a * r : ℝ) : EReal) = (r : EReal) := by
      rw [← Finset.sum_mul, hq_sum, one_mul]
    have hge : (r : EReal) ≤ ∑ a ∈ A, ((q a : ℝ) : EReal) * u a := by
      rw [← hrsum, b5246f2d_coe_sum]; exact Finset.sum_le_sum hlow
    refine ⟨hge, ?_⟩
    by_cases htop : ∃ a ∈ A, 0 < q a ∧ u a = ⊤
    · obtain ⟨a0, ha0, hq0, hu0⟩ := htop
      have hsum : ∑ a ∈ A, ((q a : ℝ) : EReal) * u a = ⊤ := by
        apply b5246f2d_sum_top A _ _ hlow a0 ha0
        rw [hu0]; exact EReal.coe_mul_top_of_pos hq0
      rw [hsum]
      constructor
      · intro h; exact absurd h.symm (EReal.coe_ne_top r)
      · intro h
        have := h a0 ha0 (by rw [hu0]; exact (EReal.coe_ne_top r).symm)
        linarith
    · simp only [not_exists, not_and] at htop
      -- every term is real
      have hterm : ∀ a ∈ A, ((q a : ℝ) : EReal) * u a = ((q a * (u a).toReal : ℝ) : EReal) := by
        intro a ha
        rcases (hq_nonneg a ha).lt_or_eq with h | h
        · have hne : u a ≠ ⊤ := fun ht => htop a ha h ht
          have hcoe : ((u a).toReal : EReal) = u a := EReal.coe_toReal hne (hu a ha)
          rw [EReal.coe_mul, hcoe]
        · rw [← h]; simp
      have hreal : ∀ a ∈ A, r ≤ (u a).toReal ∨ q a = 0 := by
        intro a ha
        rcases (hq_nonneg a ha).lt_or_eq with h | h
        · left
          have hne : u a ≠ ⊤ := fun ht => htop a ha h ht
          have hcoe : ((u a).toReal : EReal) = u a := EReal.coe_toReal hne (hu a ha)
          have h1 := hle a ha
          rw [← hcoe] at h1
          exact EReal.coe_le_coe_iff.mp h1
        · right; exact h.symm
      rw [Finset.sum_congr rfl hterm, ← b5246f2d_coe_sum, EReal.coe_eq_coe_iff]
      have hnn : ∀ a ∈ A, 0 ≤ q a * ((u a).toReal - r) := by
        intro a ha
        rcases hreal a ha with h | h
        · exact mul_nonneg (hq_nonneg a ha) (by linarith)
        · rw [h, zero_mul]
      have hdiff : ∑ a ∈ A, q a * (u a).toReal - r = ∑ a ∈ A, q a * ((u a).toReal - r) := by
        rw [show ∑ a ∈ A, q a * ((u a).toReal - r)
            = ∑ a ∈ A, q a * (u a).toReal - ∑ a ∈ A, q a * r by
              rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring]
        rw [← Finset.sum_mul, hq_sum, one_mul]
      constructor
      · intro heq a ha hne
        have h0 : ∑ a ∈ A, q a * ((u a).toReal - r) = 0 := by rw [← hdiff, heq, sub_self]
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 a ha
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · by_contra hq
          have hqp : 0 < q a := lt_of_le_of_ne (hq_nonneg a ha) (Ne.symm hq)
          have hne' : u a ≠ ⊤ := fun ht => htop a ha hqp ht
          have hcoe : ((u a).toReal : EReal) = u a := EReal.coe_toReal hne' (hu a ha)
          apply hne
          rw [← hcoe, show (u a).toReal = r by linarith]
      · intro hconc
        have h0 : ∑ a ∈ A, q a * ((u a).toReal - r) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          by_cases hua : u a = (r : EReal)
          · rw [hua, EReal.toReal_coe, sub_self, mul_zero]
          · rw [hconc a ha hua, zero_mul]
        linarith
