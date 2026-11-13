-- Prove2me | solution 1 for SymThrWires.Main.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:24:37.546586+00:00
-- url     : https://prove2.me/submissions/f380ef12-603e-415b-88db-b29622df21d8

import Mathlib

set_option autoImplicit false

/-- Moment certificates: a small `2K`-th moment forces every coordinate below `R₀`, and bounded
coordinates with `√2 R' < R₀` keep the total moment below `R₀^{2K}`. -/
theorem solution {V : Type} [Fintype V] (K : ℕ) (hK : 1 ≤ K) (hV : Fintype.card V ≤ 2 ^ K)
    (v : V → ℤ) (R₀ : ℤ) (hR₀ : 1 ≤ R₀) :
    (∑ x, v x ^ (2 * K) < R₀ ^ (2 * K) → ∀ x, |v x| < R₀) ∧
    (∀ R' : ℝ, (∀ x, |(v x : ℝ)| ≤ R') → Real.sqrt 2 * R' < (R₀ : ℝ) →
      ∑ x, v x ^ (2 * K) < R₀ ^ (2 * K)) := by
  constructor
  · intro hsum x
    by_contra hx
    push Not at hx
    have hx0 : (0 : ℤ) ≤ R₀ := by linarith
    have h1 : R₀ ^ (2 * K) ≤ |v x| ^ (2 * K) := pow_le_pow_left₀ hx0 hx (2 * K)
    have hpow : v x ^ (2 * K) = |v x| ^ (2 * K) := by
      rw [← abs_pow, abs_of_nonneg]
      exact Even.pow_nonneg (even_two_mul K) (v x)
    have h2 : R₀ ^ (2 * K) ≤ v x ^ (2 * K) := by
      simpa [← hpow] using h1
    have h3 : v x ^ (2 * K) ≤ ∑ y, v y ^ (2 * K) :=
      Finset.single_le_sum (f := fun y => v y ^ (2 * K))
        (fun y _ => Even.pow_nonneg (even_two_mul K) (v y)) (Finset.mem_univ x)
    linarith
  · intro R' hR' hsqrt
    by_cases hne : (Finset.univ : Finset V).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      have hR'nonneg : 0 ≤ R' := le_trans (abs_nonneg _) (hR' x0)
      have hterm : ∀ x, ((v x ^ (2 * K) : ℤ) : ℝ) < (R₀ : ℝ) ^ (2 * K) / 2 ^ K := by
        intro x
        have hvx : |((v x : ℝ))| ≤ R' := hR' x
        have hle : ((v x : ℝ) ^ (2 * K)) ≤ R' ^ (2 * K) := by
          have hpow : ((v x : ℝ) ^ (2 * K)) = |((v x : ℝ))| ^ (2 * K) := by
            rw [← abs_pow, abs_of_nonneg]
            exact Even.pow_nonneg (even_two_mul K) (v x : ℝ)
          rw [hpow]
          exact pow_le_pow_left₀ (abs_nonneg _) hvx (2 * K)
        have hsq : 2 * R' ^ 2 < ((R₀ : ℝ)) ^ 2 := by
          have h2 : (Real.sqrt 2 * R') ^ 2 < ((R₀ : ℝ)) ^ 2 :=
            pow_lt_pow_left₀ hsqrt (by positivity) (by norm_num)
          rwa [mul_pow, Real.sq_sqrt (by norm_num)] at h2
        have hsq' : R' ^ 2 < ((R₀ : ℝ)) ^ 2 / 2 := by linarith
        have hpow2 : R' ^ (2 * K) < ((R₀ : ℝ)) ^ (2 * K) / 2 ^ K := by
          have hK0 : K ≠ 0 := by omega
          rw [pow_mul, pow_mul, ← div_pow]
          exact pow_lt_pow_left₀ hsq' (sq_nonneg R') hK0
        rw [Int.cast_pow]
        exact lt_of_le_of_lt hle hpow2
      have hcastsum : ((∑ x, v x ^ (2 * K) : ℤ) : ℝ) = ∑ x, ((v x ^ (2 * K) : ℤ) : ℝ) :=
        Int.cast_sum Finset.univ (fun x => v x ^ (2 * K))
      have hsum_lt : ((∑ x, v x ^ (2 * K) : ℤ) : ℝ) <
          (Fintype.card V : ℝ) * (((R₀ : ℝ) ^ (2 * K)) / 2 ^ K) := by
        rw [hcastsum]
        have h := Finset.sum_lt_sum_of_nonempty
          (f := fun x => ((v x ^ (2 * K) : ℤ) : ℝ))
          (g := fun _ => ((R₀ : ℝ) ^ (2 * K)) / 2 ^ K) ⟨x0, hx0⟩ (fun x _ => hterm x)
        simpa [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using h
      have hcpos : 0 < ((R₀ : ℝ) ^ (2 * K)) / 2 ^ K := by
        have hR0pos : (0 : ℝ) < (R₀ : ℝ) := by exact_mod_cast (by linarith : (0 : ℤ) < R₀)
        positivity
      have hcard : (Fintype.card V : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hV
      have hlt : ((∑ x, v x ^ (2 * K) : ℤ) : ℝ) <
          (2 : ℝ) ^ K * (((R₀ : ℝ) ^ (2 * K)) / 2 ^ K) :=
        lt_of_lt_of_le hsum_lt (mul_le_mul_of_nonneg_right hcard hcpos.le)
      have hsimp : (2 : ℝ) ^ K * (((R₀ : ℝ) ^ (2 * K)) / 2 ^ K) = (R₀ : ℝ) ^ (2 * K) := by
        have h2 : (2 : ℝ) ^ K ≠ 0 := by positivity
        field_simp [h2]
      have hfinal : ((∑ x, v x ^ (2 * K) : ℤ) : ℝ) < ((R₀ ^ (2 * K) : ℤ) : ℝ) := by
        rw [Int.cast_pow]
        exact hsimp ▸ hlt
      exact Int.cast_lt.mp hfinal
    · have hempty : (Finset.univ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hzero : (0 : ℤ) < R₀ ^ (2 * K) :=
        pow_pos (by linarith : (0 : ℤ) < R₀) (2 * K)
      simpa [hempty] using hzero
