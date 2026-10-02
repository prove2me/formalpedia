-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.finite_class_sample_complexity_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:53:26.784595+00:00
-- url     : https://prove2.me/submissions/b6ef07c5-7b16-4219-968b-65bed5bdaf12

import Mathlib

set_option autoImplicit false

theorem p2m_sum_biUnion_le {Ω : Type*} [DecidableEq Ω] {ι : Type*} [DecidableEq ι]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (C : Finset ι) (bad : ι → Finset Ω) :
    Finset.sum (Finset.biUnion C bad) (fun ω => p ω)
      ≤ ∑ h ∈ C, Finset.sum (bad h) (fun ω => p ω) := by
  induction C using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hu := Finset.sum_union_inter (s₁ := bad a) (s₂ := s.biUnion bad) (f := fun ω => p ω)
    have hi : 0 ≤ Finset.sum (bad a ∩ s.biUnion bad) (fun ω => p ω) :=
      Finset.sum_nonneg (fun ω _ => hp ω)
    linarith

theorem solution
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ)
    (hp_nonneg : ∀ ω, 0 ≤ p ω)
    (hp_sum : Finset.sum Finset.univ (fun ω => p ω) = 1)
    {ι : Type*} [DecidableEq ι]
    (C : Finset ι)
    (bad : ι → Finset Ω)
    (m : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ)
    (hbad : ∀ h ∈ C, Finset.sum (bad h) (fun ω => p ω) ≤ (1 - ε) ^ m)
    (hm : (1 / ε) * (Real.log (C.card : ℝ) + Real.log (1 / δ)) ≤ (m : ℝ)) :
    Finset.sum (Finset.biUnion C bad) (fun ω => p ω) ≤ δ := by
  rcases C.eq_empty_or_nonempty with hC | hC
  · subst hC; simp; exact hδ0.le
  have hcard : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have h1 : Finset.sum (Finset.biUnion C bad) (fun ω => p ω)
      ≤ ∑ h ∈ C, Finset.sum (bad h) (fun ω => p ω) :=
    p2m_sum_biUnion_le p hp_nonneg C bad
  have h2 : ∑ h ∈ C, Finset.sum (bad h) (fun ω => p ω) ≤ ∑ _h ∈ C, (1 - ε) ^ m :=
    Finset.sum_le_sum hbad
  have h3 : ∑ _h ∈ C, (1 - ε) ^ m = (C.card : ℝ) * (1 - ε) ^ m := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have h4 : (1 - ε) ^ m ≤ Real.exp (-(ε * m)) := by
    have hb : (1 - ε) ≤ Real.exp (-ε) := by
      have := Real.add_one_le_exp (-ε); linarith
    calc (1 - ε) ^ m ≤ Real.exp (-ε) ^ m := pow_le_pow_left₀ (by linarith) hb m
      _ = Real.exp (-(ε * m)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
  have hlog : Real.log (C.card : ℝ) - Real.log δ ≤ ε * m := by
    have hm' := mul_le_mul_of_nonneg_left hm hε0.le
    rw [← mul_assoc, mul_one_div_cancel hε0.ne', one_mul, one_div, Real.log_inv] at hm'
    linarith
  have h5 : Real.exp (-(ε * m)) ≤ δ / (C.card : ℝ) := by
    calc Real.exp (-(ε * m)) ≤ Real.exp (Real.log δ - Real.log (C.card : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ / (C.card : ℝ) := by
        rw [Real.exp_sub, Real.exp_log hδ0, Real.exp_log hcard]
  have h6 : (C.card : ℝ) * (1 - ε) ^ m ≤ δ := by
    calc (C.card : ℝ) * (1 - ε) ^ m ≤ (C.card : ℝ) * (δ / (C.card : ℝ)) :=
          mul_le_mul_of_nonneg_left (h4.trans h5) hcard.le
      _ = δ := by field_simp
  linarith
