-- Prove2me | solution 1 for TrigPolyToComplexPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:39:27.528847+00:00
-- url     : https://prove2.me/submissions/a817a1f2-10d4-4f51-a363-d2fcf9d409ba

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyToComplexPoly

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ∃ Q : Polynomial ℂ, Q.degree ≤ (2 * m : ℕ) ∧
      ∀ t : ℝ, Q.eval (Complex.exp ((t : ℂ) * Complex.I))
        = Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I) * (T t : ℂ) := by
  obtain ⟨a, b, hrep⟩ := hT
  refine ⟨∑ k ∈ Finset.range (m + 1),
    (Polynomial.C (((a k : ℂ)) / 2)
        * (Polynomial.X ^ (m + k) + Polynomial.X ^ (m - k))
      + Polynomial.C (((b k : ℂ)) / (2 * Complex.I))
        * (Polynomial.X ^ (m + k) - Polynomial.X ^ (m - k))), ?_, ?_⟩
  · have hX : ∀ j : ℕ, j ≤ 2 * m →
        (Polynomial.X ^ j : Polynomial ℂ).degree ≤ ((2 * m : ℕ) : WithBot ℕ) := by
      intro j hj
      rw [Polynomial.degree_X_pow]
      exact_mod_cast hj
    have hCm : ∀ (c : ℂ) (f : Polynomial ℂ),
        f.degree ≤ ((2 * m : ℕ) : WithBot ℕ) →
        (Polynomial.C c * f).degree ≤ ((2 * m : ℕ) : WithBot ℕ) := by
      intro c f hf
      refine le_trans (Polynomial.degree_mul_le _ _) ?_
      calc (Polynomial.C c).degree + f.degree
          ≤ 0 + ((2 * m : ℕ) : WithBot ℕ) := add_le_add Polynomial.degree_C_le hf
        _ = ((2 * m : ℕ) : WithBot ℕ) := zero_add _
    refine le_trans (Polynomial.degree_sum_le _ _) (Finset.sup_le (fun k hk => ?_))
    have hkm : k ≤ m := by
      have h := Finset.mem_range.mp hk
      omega
    refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
    · refine hCm _ _ (le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_))
      · exact hX _ (by omega)
      · exact hX _ (by omega)
    · refine hCm _ _ (le_trans (Polynomial.degree_sub_le _ _) (max_le ?_ ?_))
      · exact hX _ (by omega)
      · exact hX _ (by omega)
  · intro t
    have hE : ∀ j : ℕ, (Complex.exp ((t : ℂ) * Complex.I)) ^ j
        = Complex.exp ((j : ℂ) * (t : ℂ) * Complex.I) := by
      intro j
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hrep t, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkm : k ≤ m := by
      have h := Finset.mem_range.mp hk
      omega
    rw [hE (m + k), hE (m - k)]
    have hmk : ((m - k : ℕ) : ℂ) = (m : ℂ) - (k : ℂ) := by
      have h : ((m - k : ℕ) : ℂ) = ((m : ℕ) : ℂ) - ((k : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub hkm]
        ring
      exact h
    have hmk2 : ((m + k : ℕ) : ℂ) = (m : ℂ) + (k : ℂ) := by push_cast; ring
    rw [hmk, hmk2]
    have hsplit1 : Complex.exp (((m : ℂ) + (k : ℂ)) * (t : ℂ) * Complex.I)
        = Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I)
          * Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hsplit2 : Complex.exp (((m : ℂ) - (k : ℂ)) * (t : ℂ) * Complex.I)
        = Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I)
          * Complex.exp (-((k : ℂ) * (t : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hck : Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I)
        = ((Real.cos ((k : ℝ) * t) : ℝ) : ℂ)
          + ((Real.sin ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
      rw [show ((k : ℂ) * (t : ℂ) * Complex.I)
          = (((((k : ℝ) * t : ℝ)) : ℂ)) * Complex.I from by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hck' : Complex.exp (-((k : ℂ) * (t : ℂ) * Complex.I))
        = ((Real.cos ((k : ℝ) * t) : ℝ) : ℂ)
          - ((Real.sin ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
      rw [show (-((k : ℂ) * (t : ℂ) * Complex.I))
          = (((-((k : ℝ) * t) : ℝ)) : ℂ) * Complex.I from by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [hsplit1, hsplit2, hck, hck']
    push_cast
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp
    ring_nf
