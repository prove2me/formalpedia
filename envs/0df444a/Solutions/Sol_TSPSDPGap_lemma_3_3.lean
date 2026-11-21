-- Prove2me | solution 1 for TSPSDPGap.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:40:24.155173+00:00
-- url     : https://prove2.me/submissions/6068d4af-5484-483d-95a7-5a723335a97d

import Mathlib

theorem solution (n : ℕ) (m : Fin n → ℂ) :
    let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun s t => m (t - s)
    let w : Fin n → ℂ := fun t =>
      Complex.exp (-2 * (Real.pi : ℂ) * ((t : ℕ) : ℂ) * Complex.I / (n : ℂ))
    let v : Fin n → Fin n → ℂ := fun t u => w t ^ (u : ℕ)
    let lam : Fin n → ℂ := fun t => ∑ s : Fin n, m s * w t ^ (s : ℕ)
    (∀ t : Fin n, M.mulVec (v t) = lam t • v t ∧ v t ≠ 0) ∧ spectrum ℂ M = Set.range lam := by
  intro M w v lam
  have hwpow : ∀ _t : Fin n, ∃ ζ : ℂ, IsPrimitiveRoot ζ n ∧ ∀ u : Fin n, w u = ζ ^ (u : ℕ) := by
    intro t
    have hn : n ≠ 0 := by have := t.2; omega
    refine ⟨(Complex.exp (2 * Real.pi * Complex.I / n))⁻¹,
      (Complex.isPrimitiveRoot_exp n hn).inv, ?_⟩
    intro u
    show Complex.exp (-2 * (Real.pi : ℂ) * ((u : ℕ) : ℂ) * Complex.I / (n : ℂ)) = _
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hpow : ∀ t : Fin n, w t ^ n = 1 := by
    intro t
    obtain ⟨ζ, hζ, hw⟩ := hwpow t
    rw [hw, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have winj : Function.Injective w := by
    intro a b hab
    obtain ⟨ζ, hζ, hw⟩ := hwpow a
    rw [hw, hw] at hab
    exact Fin.ext (hζ.pow_inj a.2 b.2 hab)
  have hmod : ∀ (z : ℂ) (k : ℕ), z ^ n = 1 → z ^ (k % n) = z ^ k := by
    intro z k hz
    conv_rhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hz, one_pow, one_mul]
  have key : ∀ t : Fin n, M.mulVec (v t) = lam t • v t := by
    intro t
    have hn : n ≠ 0 := by have := t.2; omega
    haveI : NeZero n := ⟨hn⟩
    have hm' : ∀ k : ℕ, w t ^ (k % n) = w t ^ k := fun k => hmod _ k (hpow t)
    have hsub : ∀ s r : Fin n, s + r - s = r := fun s r => add_sub_cancel_left s r
    ext s
    have e1 : (M.mulVec (v t)) s = ∑ u : Fin n, m (u - s) * w t ^ (u : ℕ) := rfl
    have e2 : (lam t • v t) s = (∑ r : Fin n, m r * w t ^ (r : ℕ)) * w t ^ (s : ℕ) := rfl
    rw [e1, e2, ← Equiv.sum_comp (Equiv.addLeft s) (fun u : Fin n => m (u - s) * w t ^ (u : ℕ))]
    simp only [Equiv.coe_addLeft, hsub, Fin.val_add, hm', pow_add]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  refine ⟨fun t => ⟨key t, ?_⟩, ?_⟩
  · intro h
    have hn : n ≠ 0 := by have := t.2; omega
    have h0 := congrFun h ⟨0, Nat.pos_of_ne_zero hn⟩
    have h1 : v t ⟨0, Nat.pos_of_ne_zero hn⟩ = 1 := by
      show w t ^ (0 : ℕ) = 1
      exact pow_zero _
    rw [h1] at h0
    exact one_ne_zero h0
  · have hV : (Matrix.transpose (Matrix.vandermonde w)).det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact Matrix.det_vandermonde_ne_zero_iff.mpr winj
    have hMV : M * Matrix.transpose (Matrix.vandermonde w)
        = Matrix.transpose (Matrix.vandermonde w) * Matrix.diagonal lam := by
      ext s t
      have e1 : (M * Matrix.transpose (Matrix.vandermonde w)) s t = (M.mulVec (v t)) s := rfl
      rw [e1, key t, Matrix.mul_diagonal]
      show lam t * w t ^ (s : ℕ) = w t ^ (s : ℕ) * lam t
      ring
    ext μ
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
    have hdet : (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - M).det = ∏ t, (μ - lam t) := by
      have hAV : (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ - M)
          * Matrix.transpose (Matrix.vandermonde w)
          = Matrix.transpose (Matrix.vandermonde w) * Matrix.diagonal (fun t => μ - lam t) := by
        rw [Algebra.algebraMap_eq_smul_one, sub_mul, Matrix.smul_mul, Matrix.one_mul, hMV]
        ext s t
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
        ring
      have hd := congrArg Matrix.det hAV
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hd
      apply mul_right_cancel₀ hV
      exact hd.trans (mul_comm _ _)
    rw [hdet, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, sub_eq_zero, Set.mem_range]
    constructor <;> rintro ⟨t, ht⟩ <;> exact ⟨t, ht.symm⟩
