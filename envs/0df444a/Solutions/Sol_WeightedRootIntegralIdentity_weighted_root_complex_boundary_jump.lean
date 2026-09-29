-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_complex_boundary_jump
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T18:57:43.24675+00:00
-- url     : https://prove2.me/submissions/766d3b15-68d4-4eb0-86fb-6a2808a58599

import Mathlib
open scoped BigOperators Interval

private lemma cpow_neg_real (r : ℝ) (hr : r < 0) (v : ℝ) :
    ((r : ℂ)) ^ ((v : ℂ))
      = ((|r| ^ v : ℝ) : ℂ) * Complex.exp (((Real.pi * v : ℝ) : ℂ) * Complex.I) := by
  have hne : (r : ℂ) ≠ 0 := by simpa using hr.ne
  have habs : (0:ℝ) < |r| := abs_pos.mpr hr.ne
  have hlog : Complex.log (r:ℂ) = ((Real.log |r| : ℝ) : ℂ) + ((Real.pi : ℝ):ℂ) * Complex.I := by
    rw [Complex.log]; simp [Complex.arg_ofReal_of_neg hr, abs_of_neg hr]
  rw [Complex.cpow_def_of_ne_zero hne, hlog, Real.rpow_def_of_pos habs, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma cpow_pos_real (r : ℝ) (hr : 0 < r) (v : ℝ) :
    ((r : ℂ)) ^ ((v : ℂ)) = ((|r| ^ v : ℝ) : ℂ) := by
  rw [abs_of_pos hr, Complex.ofReal_cpow hr.le]

theorem solution
    (n : ℕ) (a w : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1)
    (k : ℕ) (hk : k < n - 1) (x : ℝ) (hxl : a k < x) (hxr : x < a (k + 1)) :
    (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))).im
      = Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) *
          ∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i) := by
  simp only [show ∀ u v : ℝ, Real.rpow u v = u ^ v from fun _ _ => rfl]
  have hkn : k + 1 ≤ n := by omega
  -- monotonicity along the chain
  have hmono' : ∀ j, j ≤ n - 1 → ∀ i, i ≤ j → a i ≤ a j := by
    intro j
    induction j with
    | zero => intro _ i hi; have : i = 0 := Nat.le_zero.mp hi; simp [this]
    | succ m ih =>
        intro hj i hi
        rcases Nat.eq_or_lt_of_le hi with h | h
        · rw [h]
        · exact le_trans (ih (by omega) i (by omega)) (hmono m (by omega))
  -- the two sign regimes
  have hposfac : ∀ i ∈ Finset.Ico 0 (k+1), 0 < x - a i := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have : a i ≤ a k := hmono' k (by omega) i (by omega)
    linarith
  have hnegfac : ∀ i ∈ Finset.Ico (k+1) n, x - a i < 0 := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have : a (k+1) ≤ a i := hmono' i (by omega) (k+1) hi.1
    linarith
  set H : ℝ := ∏ i ∈ Finset.range n, |x - a i| ^ w i with hH
  set S : ℝ := ∑ i ∈ Finset.Ico (k+1) n, w i with hS
  -- factorisation of the complex product
  have hprod : (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ)))
      = (H : ℂ) * Complex.exp (((Real.pi * S : ℝ) : ℂ) * Complex.I) := by
    have hsplitC :
        (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ)))
          = (∏ i ∈ Finset.Ico 0 (k+1), ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ)))
            * (∏ i ∈ Finset.Ico (k+1) n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))) := by
      rw [Finset.prod_Ico_consecutive _ (Nat.zero_le _) hkn, Finset.range_eq_Ico]
    have hsplitR :
        H = (∏ i ∈ Finset.Ico 0 (k+1), |x - a i| ^ w i)
            * (∏ i ∈ Finset.Ico (k+1) n, |x - a i| ^ w i) := by
      rw [hH, Finset.prod_Ico_consecutive _ (Nat.zero_le _) hkn, Finset.range_eq_Ico]
    have hleft : (∏ i ∈ Finset.Ico 0 (k+1), ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ)))
        = ((∏ i ∈ Finset.Ico 0 (k+1), |x - a i| ^ w i : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl ?_
      intro i hi
      have : ((x : ℂ) - (a i : ℂ)) = ((x - a i : ℝ) : ℂ) := by push_cast; ring
      rw [this, cpow_pos_real _ (hposfac i hi)]
    have hright : (∏ i ∈ Finset.Ico (k+1) n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ)))
        = ((∏ i ∈ Finset.Ico (k+1) n, |x - a i| ^ w i : ℝ) : ℂ)
            * Complex.exp (((Real.pi * S : ℝ) : ℂ) * Complex.I) := by
      have : ∀ i ∈ Finset.Ico (k+1) n,
          ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))
            = ((|x - a i| ^ w i : ℝ) : ℂ) * Complex.exp (((Real.pi * w i : ℝ) : ℂ) * Complex.I) := by
        intro i hi
        have hc : ((x : ℂ) - (a i : ℂ)) = ((x - a i : ℝ) : ℂ) := by push_cast; ring
        rw [hc, cpow_neg_real _ (hnegfac i hi)]
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Complex.ofReal_prod,
        ← Complex.exp_sum]
      congr 1
      rw [← Finset.sum_mul]
      congr 1
      rw [hS, ← Complex.ofReal_sum]
      push_cast
      rw [Finset.mul_sum]
    rw [hsplitC, hleft, hright, hsplitR]
    push_cast
    ring
  rw [hprod]
  have him : ((H : ℂ) * Complex.exp (((Real.pi * S : ℝ) : ℂ) * Complex.I)).im
      = H * Real.sin (Real.pi * S) := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
    ring
  rw [him]
  have hSval : S = 1 - ∑ i ∈ Finset.range (k+1), w i := by
    have h := Finset.sum_Ico_consecutive w (Nat.zero_le (k+1)) hkn
    simp only [← Finset.range_eq_Ico] at h
    rw [hwsum, ← hS] at h
    linarith
  rw [hSval]
  have hpi : Real.pi * (1 - ∑ i ∈ Finset.range (k+1), w i)
      = Real.pi - Real.pi * (∑ i ∈ Finset.range (k+1), w i) := by ring
  rw [hpi, Real.sin_pi_sub]
  ring
