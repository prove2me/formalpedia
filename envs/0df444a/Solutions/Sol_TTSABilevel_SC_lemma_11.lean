-- Prove2me | solution 1 for TTSABilevel.SC.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:05:54.708998+00:00
-- url     : https://prove2.me/submissions/4b0cdb59-7e0c-45a6-a338-ea3b27b3ec23

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (γ ρ : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hγmono : Antitone γ) (hρmono : Antitone ρ)
    (hγnonneg : ∀ j, 0 ≤ γ j) (hρnonneg : ∀ j, 0 ≤ ρ j)
    (hscale : ∀ j, 2 * a * γ j ≤ b * ρ j)
    (hfirst : ρ 0 < 1 / b) :
    ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1),
        γ j * (∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) *
          (∏ i ∈ Finset.range (j + 1), (1 - ρ i * b))) ≤
        1 / a * (∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a)) := by
  intro k
  have hρb : ∀ i, ρ i * b < 1 := by
    intro i
    have h1 : ρ i ≤ ρ 0 := hρmono (Nat.zero_le i)
    have h2 : ρ 0 * b < 1 := by
      have := (lt_div_iff₀ hb).mp hfirst
      exact this
    nlinarith
  have hA : ∀ i, 0 ≤ 1 - γ i * a := by
    intro i
    have := hscale i
    have := hρb i
    nlinarith
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, ∀ j, A j = ∏ i ∈ Finset.range (j + 1), (1 - γ i * a) :=
    ⟨fun j => ∏ i ∈ Finset.range (j + 1), (1 - γ i * a), fun j => rfl⟩
  have hA0 : ∀ j, 0 ≤ A j := fun j => by
    rw [hAdef]; exact Finset.prod_nonneg (fun i _ => hA i)
  have hsplit : ∀ j, j ≤ k →
      (∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) * A j =
        ∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a) := by
    intro j hj
    rw [mul_comm, hAdef]
    have hI : Finset.Icc (j + 1) k = Finset.Ico (j + 1) (k + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI]
    exact Finset.prod_range_mul_prod_Ico _ (by omega)
  -- bound on Q
  have hQ : ∀ j, (∏ i ∈ Finset.range (j + 1), (1 - ρ i * b)) ≤ A j ^ 2 := by
    intro j
    rw [hAdef, ← Finset.prod_pow]
    apply Finset.prod_le_prod
    · intro i _
      have := hρb i
      linarith
    · intro i _
      have := hscale i
      nlinarith [hγnonneg i, sq_nonneg (γ i * a)]
  -- telescoping
  have htel : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), γ j * A j) ≤ (1 - A n) / a := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton]
      have : A 0 = 1 - γ 0 * a := by simp [hAdef]
      rw [this, le_div_iff₀ ha]
      nlinarith [sq_nonneg (γ 0 * a)]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hAs : A (n + 1) = A n * (1 - γ (n + 1) * a) := by
        rw [hAdef, hAdef, Finset.prod_range_succ (n := n + 1)]
      have hle : γ (n + 1) * A (n + 1) ≤ (A n - A (n + 1)) / a := by
        rw [le_div_iff₀ ha, hAs]
        nlinarith [mul_nonneg (hA0 n) (sq_nonneg (γ (n + 1) * a))]
      have e : (1 - A n) / a + (A n - A (n + 1)) / a = (1 - A (n + 1)) / a := by
        rw [← add_div]; ring_nf
      linarith
  have hP0 : 0 ≤ ∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a) :=
    Finset.prod_nonneg (fun i _ => hA i)
  calc (∑ j ∈ Finset.range (k + 1),
        γ j * (∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) *
          (∏ i ∈ Finset.range (j + 1), (1 - ρ i * b)))
      ≤ ∑ j ∈ Finset.range (k + 1),
          (γ j * A j) * ∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
        have hs := hsplit j hjk
        have hP : 0 ≤ ∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a) :=
          Finset.prod_nonneg (fun i _ => hA i)
        have hg := hγnonneg j
        calc γ j * (∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) *
              (∏ i ∈ Finset.range (j + 1), (1 - ρ i * b))
            ≤ γ j * (∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) * A j ^ 2 :=
              mul_le_mul_of_nonneg_left (hQ j) (mul_nonneg hg hP)
          _ = (γ j * A j) * ((∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) * A j) := by ring
          _ = _ := by rw [hs]
    _ = (∑ j ∈ Finset.range (k + 1), γ j * A j) *
          ∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a) := by rw [Finset.sum_mul]
    _ ≤ (1 / a) * ∏ ℓ ∈ Finset.range (k + 1), (1 - γ ℓ * a) := by
        apply mul_le_mul_of_nonneg_right _ hP0
        have := htel k
        have h2 : (1 - A k) / a ≤ 1 / a := by
          apply div_le_div_of_nonneg_right _ ha.le
          linarith [hA0 k]
        linarith
