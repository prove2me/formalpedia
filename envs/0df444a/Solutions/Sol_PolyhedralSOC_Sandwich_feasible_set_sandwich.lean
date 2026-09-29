-- Prove2me | solution 1 for PolyhedralSOC.Sandwich.feasible_set_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T14:35:23.815707+00:00
-- url     : https://prove2.me/submissions/0f382d30-3f12-460e-9b89-44d7f35d27b3

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP
import Definitions.Def_PolyhedralSOC_Sandwich_Conditions

open Matrix

namespace PolyhedralSOC.Sandwich

lemma eucNorm_eq {k : ℕ} (w : Fin k → ℝ) :
    eucNorm w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin k))‖ := by
  rw [EuclideanSpace.norm_eq]; simp [eucNorm, Real.norm_eq_abs, sq_abs]

lemma eucNorm_nonneg {k : ℕ} (w : Fin k → ℝ) : 0 ≤ eucNorm w := by
  rw [eucNorm_eq]; exact norm_nonneg _

lemma eucNorm_comb {k : ℕ} (u v : Fin k → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    eucNorm (a • u + b • v) ≤ a * eucNorm u + b * eucNorm v := by
  rw [eucNorm_eq, eucNorm_eq, eucNorm_eq, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
  calc _ ≤ ‖a • (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin k))‖ +
        ‖b • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin k))‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg hb]

lemma aff_vec {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) (v : Fin k → ℝ) (x y : Fin n → ℝ)
    {a b : ℝ} (hab : a + b = 1) :
    M *ᵥ (a • x + b • y) - v = a • (M *ᵥ x - v) + b • (M *ᵥ y - v) := by
  rw [mulVec_add, mulVec_smul, mulVec_smul]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (v i) * hab

lemma aff_dot {n : ℕ} (c x y : Fin n → ℝ) (d : ℝ) {a b : ℝ} (hab : a + b = 1) :
    c ⬝ᵥ (a • x + b • y) - d = a * (c ⬝ᵥ x - d) + b * (c ⬝ᵥ y - d) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  linear_combination d * hab

lemma aff_lin {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) (v : Fin k → ℝ) (x y : Fin n → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : ∀ i, v i ≤ (M *ᵥ x) i) (hy : ∀ i, v i ≤ (M *ᵥ y) i) :
    ∀ i, v i ≤ (M *ᵥ (a • x + b • y)) i := by
  intro i
  rw [mulVec_add, mulVec_smul, mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : v i = a * v i + b * v i := by linear_combination (-(v i)) * hab
  linarith [mul_le_mul_of_nonneg_left (hx i) ha, mul_le_mul_of_nonneg_left (hy i) hb]

/-- conic constraint for a convex combination -/
lemma conic_comb {n k₀ m : ℕ} (P : CQP n k₀ m) (ℓ : Fin m) (x y : Fin n → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    eucNorm (P.Aℓ ℓ *ᵥ (a • x + b • y) - P.bℓ ℓ) ≤
      a * eucNorm (P.Aℓ ℓ *ᵥ x - P.bℓ ℓ) + b * eucNorm (P.Aℓ ℓ *ᵥ y - P.bℓ ℓ) := by
  rw [aff_vec _ _ _ _ hab]; exact eucNorm_comb _ _ ha hb

theorem sandwich_main {n k₀ m : ℕ} (P : CQP n k₀ m) (hm : 0 < m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (R : ℝ) (hii : IsSemibounded P R)
    (ε : ℝ) (hε : 0 < ε) (hγ : R * ε / r < 1) :
    (fun y => (R * ε / r) • xbar + (1 - R * ε / r) • y) '' feasRelaxed P ε ⊆ feas P ∧
      feas P ⊆ feasRelaxed P ε := by
  obtain ⟨hr, hxlin, hxcon⟩ := hi
  set t : Fin m → (Fin n → ℝ) → ℝ := fun ℓ x => P.c ℓ ⬝ᵥ x - P.d ℓ with htdef
  have hxfeas : xbar ∈ feas P := ⟨hxlin, fun ℓ => by linarith [hxcon ℓ]⟩
  have htbar : ∀ ℓ, r ≤ t ℓ xbar := fun ℓ => by
    have := hxcon ℓ; have := eucNorm_nonneg (P.Aℓ ℓ *ᵥ xbar - P.bℓ ℓ); simp only [htdef]; linarith
  set ℓ0 : Fin m := ⟨0, hm⟩
  have hRr : r ≤ R := (htbar ℓ0).trans (hii xbar hxfeas ℓ0)
  have hR0 : 0 < R := lt_of_lt_of_le hr hRr
  refine ⟨?_, fun x hx => ⟨hx.1, fun ℓ => ?_⟩⟩
  swap
  · have h1 := hx.2 ℓ
    have h2 := eucNorm_nonneg (P.Aℓ ℓ *ᵥ x - P.bℓ ℓ)
    nlinarith
  rintro _ ⟨y, ⟨hylin, hycon⟩, rfl⟩
  set γ := R * ε / r with hγdef
  have hγ0 : 0 ≤ γ := by positivity
  have hγr : γ * r = R * ε := by rw [hγdef]; field_simp
  have hty0 : ∀ ℓ, 0 ≤ t ℓ y := fun ℓ => by
    have h1 := hycon ℓ; have h2 := eucNorm_nonneg (P.Aℓ ℓ *ᵥ y - P.bℓ ℓ)
    simp only [htdef]; nlinarith
  -- the largest value of `t ℓ y`
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨ℓ0, Finset.mem_univ _⟩
  set T := Finset.univ.sup' hne (fun ℓ => t ℓ y) with hTdef
  have hT : ∀ ℓ, t ℓ y ≤ T := fun ℓ => Finset.le_sup' (fun ℓ => t ℓ y) (Finset.mem_univ ℓ)
  obtain ⟨ℓ1, -, hℓ1⟩ := Finset.exists_mem_eq_sup' hne (fun ℓ => t ℓ y)
  have hT0 : 0 ≤ T := (hty0 ℓ0).trans (hT ℓ0)
  -- an auxiliary feasible point
  set μ := r / (r + ε * T) with hμdef
  have hden : 0 < r + ε * T := by positivity
  have hμ0 : 0 < μ := by positivity
  have hμ1 : μ ≤ 1 := by rw [hμdef, div_le_one hden]; nlinarith
  have hμkey : μ * (ε * T) = (1 - μ) * r := by rw [hμdef]; field_simp; ring
  have hwfeas : (1 - μ) • xbar + μ • y ∈ feas P := by
    refine ⟨aff_lin _ _ _ _ (by linarith) hμ0.le (by ring) hxlin hylin, fun ℓ => ?_⟩
    have h1 := conic_comb P ℓ xbar y (by linarith : 0 ≤ 1 - μ) hμ0.le (by ring)
    rw [aff_dot _ _ _ _ (by ring : (1 - μ) + μ = 1)]
    have h2 := mul_le_mul_of_nonneg_left (hxcon ℓ) (by linarith : 0 ≤ 1 - μ)
    have h3 := mul_le_mul_of_nonneg_left (hycon ℓ) hμ0.le
    have h4 : μ * (ε * t ℓ y) ≤ μ * (ε * T) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT ℓ) hε.le) hμ0.le
    simp only [htdef] at h4 hμkey
    nlinarith
  have hbound := hii _ hwfeas ℓ1
  rw [aff_dot _ _ _ _ (by ring : (1 - μ) + μ = 1)] at hbound
  have hℓ1' : P.c ℓ1 ⬝ᵥ y - P.d ℓ1 = T := hℓ1.symm
  rw [hℓ1'] at hbound
  have hb2 : (1 - μ) * r + μ * T ≤ R := by
    have := mul_le_mul_of_nonneg_left (htbar ℓ1) (by linarith : 0 ≤ 1 - μ)
    simp only [htdef] at this; linarith
  -- (1 - γ) T ≤ R
  have hTR : (1 - γ) * T ≤ R := by
    have e1 : ((1 - μ) * r + μ * T) * (r + ε * T) = r * (ε * T) + r * T := by
      rw [hμdef]; field_simp; ring
    have h5 : r * (ε * T) + r * T ≤ R * (r + ε * T) := by
      rw [← e1]; exact mul_le_mul_of_nonneg_right hb2 hden.le
    have h6 : r * ((1 - γ) * T) ≤ r * R := by
      have : r * ((1 - γ) * T) = r * T - R * ε * T := by rw [← hγr]; ring
      rw [this]; linarith [mul_nonneg (mul_nonneg hr.le hε.le) hT0]
    exact le_of_mul_le_mul_left h6 hr
  refine ⟨aff_lin _ _ _ _ hγ0 (by linarith) (by ring) hxlin hylin, fun ℓ => ?_⟩
  have h1 := conic_comb P ℓ xbar y hγ0 (by linarith : 0 ≤ 1 - γ) (by ring)
  rw [aff_dot _ _ _ _ (by ring : γ + (1 - γ) = 1)]
  have h2 := mul_le_mul_of_nonneg_left (hxcon ℓ) hγ0
  have h3 := mul_le_mul_of_nonneg_left (hycon ℓ) (by linarith : 0 ≤ 1 - γ)
  have h4 : (1 - γ) * (ε * t ℓ y) ≤ (1 - γ) * (ε * T) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT ℓ) hε.le) (by linarith)
  have h5 : (1 - γ) * (ε * T) ≤ ε * R := by nlinarith
  simp only [htdef] at h4
  nlinarith

end PolyhedralSOC.Sandwich

open PolyhedralSOC.Sandwich

theorem solution {n k₀ m : ℕ} (P : CQP n k₀ m) (hm : 0 < m)
    (xbar : Fin n → ℝ) (r : ℝ) (hi : IsStrictlyFeasible P xbar r)
    (R : ℝ) (hii : IsSemibounded P R)
    (ε : ℝ) (hε : 0 < ε) (hγ : R * ε / r < 1) :
    (fun y => (R * ε / r) • xbar + (1 - R * ε / r) • y) '' feasRelaxed P ε ⊆ feas P ∧
      feas P ⊆ feasRelaxed P ε := by
  exact sandwich_main P hm xbar r hi R hii ε hε hγ
