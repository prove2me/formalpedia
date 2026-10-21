-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:21:58.648121+00:00
-- url     : https://prove2.me/submissions/c656bb22-3bb2-42ed-84fd-bba3b4050e57

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

theorem g64f_comm_of_normal {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] (h : ∀ a : A, a * star a = star a * a) (a b : A) :
    b * star a = star a * b := by
  have h1 := h (a + b)
  have h2 := h (a + Complex.I • b)
  have ha := h a
  have hb := h b
  rw [star_add, star_smul, Complex.star_def, Complex.conj_I] at h2
  rw [star_add] at h1
  have e1 : (a + b) * (star a + star b) - (star a + star b) * (a + b) =
      (a * star a - star a * a) + (b * star b - star b * b) +
        (a * star b + b * star a - star a * b - star b * a) := by
    simp only [add_mul, mul_add]; abel
  have e2 : (a + Complex.I • b) * (star a + (-Complex.I) • star b) -
      (star a + (-Complex.I) • star b) * (a + Complex.I • b) =
      (a * star a - star a * a) + (b * star b - star b * b) +
        Complex.I • (-(a * star b) + b * star a - star a * b + star b * a) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
      neg_mul, mul_neg, Complex.I_mul_I, neg_neg]
    module
  rw [h1, sub_self, ha, hb, sub_self, sub_self, zero_add, zero_add] at e1
  rw [h2, sub_self, ha, hb, sub_self, sub_self, zero_add, zero_add] at e2
  have e2' : -(a * star b) + b * star a - star a * b + star b * a = 0 := by
    have := congrArg (fun x => (-Complex.I) • x) e2
    simp only [smul_zero, smul_smul] at this
    rw [neg_mul, Complex.I_mul_I, neg_neg, one_smul] at this
    exact this.symm
  have : (2:ℂ) • (b * star a - star a * b) = 0 := by
    rw [two_smul]
    have := congrArg₂ (· + ·) e1.symm e2'
    simp only [add_zero] at this
    rw [← this]; abel
  have := (smul_eq_zero.mp this).resolve_left (by norm_num)
  exact sub_eq_zero.mp this

theorem g64f_part2 {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (R : Subalgebra ℝ A)
    (hR : Function.Surjective (fun p : R × R => (p.1 : A) + Complex.I • (p.2 : A)))
    (hs : ∀ a : R, star (a : A) = (a : A)) (a b : A) : a * b = b * a := by
  have hc : ∀ x y : R, (x : A) * y = y * x := by
    intro x y
    have h := hs (x * y)
    rw [Subalgebra.coe_mul, star_mul, hs, hs] at h
    exact h.symm
  obtain ⟨⟨r1, r2⟩, rfl⟩ := hR a
  obtain ⟨⟨s1, s2⟩, rfl⟩ := hR b
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hc r1 s1, hc r1 s2, hc r2 s1, hc r2 s2]
  module

theorem solution {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] :
    ((∀ a b : A, a * b = b * a) ↔ ∀ a : A, a * star a = star a * a) ∧
    (∀ R : Subalgebra ℝ A, IsRealForm R →
      (∀ a : R, star (a : A) = (a : A)) → ∀ a b : A, a * b = b * a) := by
  refine ⟨⟨fun h a => h a (star a), fun h a b => ?_⟩, fun R hR hs a b => g64f_part2 R hR.2 hs a b⟩
  have := g64f_comm_of_normal h (star a) b
  rwa [star_star, eq_comm] at this
