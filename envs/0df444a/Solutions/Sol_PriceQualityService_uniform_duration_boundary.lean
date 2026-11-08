-- Prove2me | solution 1 for PriceQualityService.uniform_duration_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T03:51:41.3802+00:00
-- url     : https://prove2.me/submissions/179e614a-6188-473f-8506-46da08780e5d

import Mathlib
import Definitions.Def_PriceQualityService_IsOptimalUniform

set_option autoImplicit false

namespace PQSUniformAux

open PriceQualityService

lemma profit_eq {N : ℕ} (α s a b c p q : Fin N → ℝ) (t : ℝ) :
    profit α s a b c p q (fun _ => t) =
      (∑ i, margin a b c p q (fun _ => t) i * Real.exp (utility α s p q (fun _ => t) i)) /
        (1 + ∑ j, Real.exp (utility α s p q (fun _ => t) j)) := by
  unfold profit choiceProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- MNL upper bound: any markups give profit at most `R - 1`, where `R - 1 = X e^{-R}`. -/
lemma mnl_bound {N : ℕ} (m v : Fin N → ℝ) (R : ℝ)
    (hR : R - 1 = (∑ i, Real.exp (v i)) * Real.exp (-R)) :
    (∑ i, m i * Real.exp (v i - m i)) / (1 + ∑ j, Real.exp (v j - m j)) ≤ R - 1 := by
  have hpos : 0 < 1 + ∑ j, Real.exp (v j - m j) := by
    have : 0 ≤ ∑ j, Real.exp (v j - m j) :=
      Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
    linarith
  rw [div_le_iff₀ hpos]
  have key : ∀ i, m i * Real.exp (v i - m i) - (R - 1) * Real.exp (v i - m i)
      ≤ Real.exp (v i) * Real.exp (-R) := by
    intro i
    have h1 := Real.add_one_le_exp (m i - R)
    have h2 := Real.exp_pos (v i - m i)
    have h3 : Real.exp (m i - R) * Real.exp (v i - m i) = Real.exp (v i) * Real.exp (-R) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h4 := mul_le_mul_of_nonneg_right h1 h2.le
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hs
  nlinarith

lemma root_exists {X : ℝ} (hX : 0 < X) : ∃ R : ℝ, 1 < R ∧ R - 1 = X * Real.exp (-R) := by
  have hcont : ContinuousOn (fun m : ℝ => m - 1 - X * Real.exp (-m)) (Set.Icc 1 (1 + X)) := by
    fun_prop
  have h1 : (fun m : ℝ => m - 1 - X * Real.exp (-m)) 1 ≤ 0 := by
    simp only
    have := Real.exp_pos (-1)
    nlinarith
  have h2 : 0 ≤ (fun m : ℝ => m - 1 - X * Real.exp (-m)) (1 + X) := by
    simp only
    have : Real.exp (-(1 + X)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  obtain ⟨m, _, hm⟩ := intermediate_value_Icc (by linarith) hcont ⟨h1, h2⟩
  have hm' : m - 1 = X * Real.exp (-m) := by simp only at hm; linarith
  refine ⟨m, ?_, hm'⟩
  have : 0 < X * Real.exp (-m) := mul_pos hX (Real.exp_pos _)
  linarith

/-- Tangent-line bound for a sum of exponentials, strict when some slope is nonzero. -/
lemma tangent_lt {N : ℕ} (G h : Fin N → ℝ) (t τ : ℝ) (k : Fin N) (hk : h k ≠ 0) (hτ : τ ≠ t) :
    (∑ i, Real.exp (G i + t * h i)) + (τ - t) * (∑ i, Real.exp (G i + t * h i) * h i)
      < ∑ i, Real.exp (G i + τ * h i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsplit : ∀ i, Real.exp (G i + τ * h i)
      = Real.exp (G i + t * h i) * Real.exp ((τ - t) * h i) := by
    intro i; rw [← Real.exp_add]; ring_nf
  apply Finset.sum_lt_sum
  · intro i _
    rw [hsplit i]
    have h1 := Real.add_one_le_exp ((τ - t) * h i)
    have h2 := Real.exp_pos (G i + t * h i)
    nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]
  · refine ⟨k, Finset.mem_univ k, ?_⟩
    rw [hsplit k]
    have hne : (τ - t) * h k ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hτ) hk
    have h1 := Real.add_one_lt_exp hne
    have h2 := Real.exp_pos (G k + t * h k)
    nlinarith [mul_lt_mul_of_pos_left h1 h2]

lemma convex_endpoint {N : ℕ} (G h : Fin N → ℝ) (ts t tl : ℝ) (h1 : ts < t) (h2 : t < tl)
    (k : Fin N) (hk : h k ≠ 0) :
    ∃ τ ∈ Set.Icc ts tl, (∑ i, Real.exp (G i + t * h i)) < ∑ i, Real.exp (G i + τ * h i) := by
  by_cases hD : 0 ≤ ∑ i, Real.exp (G i + t * h i) * h i
  · refine ⟨tl, ⟨by linarith, le_refl _⟩, ?_⟩
    have := tangent_lt G h t tl k hk (ne_of_gt h2)
    nlinarith
  · refine ⟨ts, ⟨le_refl _, by linarith⟩, ?_⟩
    have := tangent_lt G h t ts k hk (ne_of_lt h1)
    push_neg at hD
    nlinarith

theorem main {N : ℕ} (α s a b c : Fin N → ℝ) (Q : Set (Fin N → ℝ))
    (ts tl : ℝ) (p q : Fin N → ℝ) (t : ℝ)
    (hopt : IsOptimalUniform α s a b c Q ts tl p q t) :
    t = ts ∨ t = tl ∨
      ∀ t' ∈ Set.Icc ts tl, ∃ p' : Fin N → ℝ, IsOptimalUniform α s a b c Q ts tl p' q t' := by
  obtain ⟨hq, ht, hmax⟩ := hopt
  by_cases e1 : t = ts
  · exact Or.inl e1
  by_cases e2 : t = tl
  · exact Or.inr (Or.inl e2)
  right; right
  have hts : ts < t := lt_of_le_of_ne ht.1 (Ne.symm e1)
  have htl : t < tl := lt_of_le_of_ne ht.2 e2
  obtain ⟨h, hh⟩ : ∃ h : Fin N → ℝ, h = fun i => s i - a i + b i * q i := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Fin N → ℝ, G = fun i => α i * q i - c i * q i ^ 2 := ⟨_, rfl⟩
  have hu : ∀ (p : Fin N → ℝ) (τ : ℝ) (i : Fin N), utility α s p q (fun _ => τ) i
      = (G i + τ * h i) - margin a b c p q (fun _ => τ) i := by
    intro p τ i; subst hh hG; simp only [utility, margin]; ring
  have hzero : ∀ i, h i = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨k, hk⟩ := hne
    have hXpos : 0 < ∑ i, Real.exp (G i + t * h i) :=
      Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨k, Finset.mem_univ k⟩
    obtain ⟨R, hR1, hR⟩ := root_exists hXpos
    have hV : profit α s a b c p q (fun _ => t) ≤ R - 1 := by
      rw [profit_eq]
      have := mnl_bound (fun i => margin a b c p q (fun _ => t) i) (fun i => G i + t * h i) R hR
      simp only [hu]
      exact this
    obtain ⟨τ, hτ, hlt⟩ := convex_endpoint G h ts t tl hts htl k hk
    obtain ⟨p2, hp2⟩ : ∃ p2 : Fin N → ℝ,
        p2 = fun i => R + c i * q i ^ 2 + τ * (a i - b i * q i) := ⟨_, rfl⟩
    have hm2 : ∀ i, margin a b c p2 q (fun _ => τ) i = R := by
      intro i; subst hp2; simp only [margin]; ring
    have hprof : profit α s a b c p2 q (fun _ => τ)
        = (R * ((∑ i, Real.exp (G i + τ * h i)) * Real.exp (-R)))
          / (1 + (∑ i, Real.exp (G i + τ * h i)) * Real.exp (-R)) := by
      rw [profit_eq]
      simp only [hu, hm2]
      have hex : ∀ i, Real.exp (G i + τ * h i - R) = Real.exp (G i + τ * h i) * Real.exp (-R) := by
        intro i; rw [← Real.exp_add]; ring_nf
      simp only [hex]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    have hk2 : (R - 1) < (∑ i, Real.exp (G i + τ * h i)) * Real.exp (-R) := by
      rw [hR]; exact mul_lt_mul_of_pos_right hlt (Real.exp_pos _)
    have hgt : R - 1 < profit α s a b c p2 q (fun _ => τ) := by
      rw [hprof]
      have hpos : 0 < 1 + (∑ i, Real.exp (G i + τ * h i)) * Real.exp (-R) := by linarith
      rw [lt_div_iff₀ hpos]
      nlinarith
    have := hmax p2 q τ hq hτ
    linarith
  intro t' ht'
  obtain ⟨p', hp'⟩ : ∃ p' : Fin N → ℝ,
      p' = fun i => p i + (t' - t) * (a i - b i * q i) := ⟨_, rfl⟩
  have hmeq : ∀ i, margin a b c p' q (fun _ => t') i = margin a b c p q (fun _ => t) i := by
    intro i; subst hp'; simp only [margin]; ring
  have hueq : ∀ i, utility α s p' q (fun _ => t') i = utility α s p q (fun _ => t) i := by
    intro i
    have hz := hzero i
    subst hp' hh
    simp only [utility] at hz ⊢
    linear_combination (t' - t) * hz
  have heq : profit α s a b c p' q (fun _ => t') = profit α s a b c p q (fun _ => t) := by
    rw [profit_eq, profit_eq]
    simp only [hmeq, hueq]
  refine ⟨p', hq, ht', fun p'' q'' t'' hq'' ht'' => ?_⟩
  rw [heq]
  exact hmax p'' q'' t'' hq'' ht''

end PQSUniformAux

open PriceQualityService in
theorem solution {N : ℕ} (α s a b c : Fin N → ℝ) (Q : Set (Fin N → ℝ))
    (ts tl : ℝ) (p q : Fin N → ℝ) (t : ℝ)
    (hopt : IsOptimalUniform α s a b c Q ts tl p q t) :
    t = ts ∨ t = tl ∨
      ∀ t' ∈ Set.Icc ts tl, ∃ p' : Fin N → ℝ, IsOptimalUniform α s a b c Q ts tl p' q t' := by
  exact PQSUniformAux.main α s a b c Q ts tl p q t hopt
