-- Prove2me | solution 1 for PsdPermanent.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:13:02.387911+00:00
-- url     : https://prove2.me/submissions/0ea87772-2614-4b07-acd3-b3e2179df52a

import Mathlib
import Definitions.Def_PsdPermanent_phi

open Matrix

open scoped ComplexOrder

namespace Aux_Q01_lemma_8

theorem diag_re_pos {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (hV : ∀ i, V i ≠ 0)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef) (i : Fin n) :
    0 < ((V * X * Vᴴ) i i).re := by
  have hw0 : (fun k => star (V i k)) ≠ 0 := by
    intro h
    apply hV i
    funext k
    have := congrFun h k
    simpa using this
  have hpos := hX.dotProduct_mulVec_pos hw0
  have heq : (V * X * Vᴴ) i i =
      star (fun k => star (V i k)) ⬝ᵥ (X *ᵥ (fun k => star (V i k))) := by
    simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, Pi.star_apply,
      star_star, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  rw [heq]
  exact (Complex.pos_iff.mp hpos).1

end Aux_Q01_lemma_8

open PsdPermanent in
theorem solution {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (hrank : V.rank = d) (hV : ∀ i, V i ≠ 0)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef)
    (hmax : ∀ Y : Matrix (Fin d) (Fin d) ℂ, Y.PosDef → phi V Y ≤ phi V X) :
    X.trace = (n : ℂ) + d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Matrix.trace]
    · exfalso
      exact hV ⟨0, hn⟩ (Subsingleton.elim _ _)
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨hτ, hτim⟩ := Complex.pos_iff.mp hX.trace_pos
  have hdet : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have ha : ∀ i, 0 < ((V * X * Vᴴ) i i).re := Aux_Q01_lemma_8.diag_re_pos V hV X hX
  have key : ∀ t : ℝ, 0 < t → ((n : ℝ) + d) * Real.log t ≤ (t - 1) * X.trace.re := by
    intro t ht
    have hY : ((t : ℂ) • X).PosDef := hX.smul (Complex.zero_lt_real.mpr ht)
    have h := hmax _ hY
    unfold phi at h
    have e1 : ∀ i, ((V * ((t : ℂ) • X) * Vᴴ) i i).re = t * ((V * X * Vᴴ) i i).re := by
      intro i
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    have e2 : (((t : ℂ) • X).det).re = t ^ d * X.det.re := by
      rw [Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have e3 : (((t : ℂ) • X).trace).re = t * X.trace.re := by
      rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    simp only [e1, e2, e3] at h
    rw [Real.log_mul (pow_pos ht d).ne' hdet.ne', Real.log_pow] at h
    have hs : ∑ i, Real.log (t * ((V * X * Vᴴ) i i).re) =
        ∑ i, (Real.log t + Real.log ((V * X * Vᴴ) i i).re) :=
      Finset.sum_congr rfl (fun i _ => Real.log_mul ht.ne' (ha i).ne')
    rw [hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : (0 : ℝ) < (n : ℝ) + d := by positivity
  have hk := key (((n : ℝ) + d) / X.trace.re) (div_pos hm hτ)
  rw [sub_mul, div_mul_cancel₀ _ hτ.ne', one_mul] at hk
  have hl : Real.log (((n : ℝ) + d) / X.trace.re) = - Real.log (X.trace.re / ((n : ℝ) + d)) := by
    rw [← Real.log_inv, inv_div]
  rw [hl] at hk
  have hu : 0 < X.trace.re / ((n : ℝ) + d) := div_pos hτ hm
  have hτu : X.trace.re = ((n : ℝ) + d) * (X.trace.re / ((n : ℝ) + d)) :=
    (mul_div_cancel₀ _ hm.ne').symm
  have hu1 : X.trace.re / ((n : ℝ) + d) = 1 := by
    by_contra hne
    have hlt := Real.log_lt_sub_one_of_pos hu hne
    nlinarith [mul_pos hm (sub_pos.mpr hlt)]
  have hτm : X.trace.re = (n : ℝ) + d := by
    rw [hτu, hu1, mul_one]
  have htr : X.trace = ((X.trace.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact hτim.symm)
  rw [htr, hτm]
  first
    | norm_num
    | (push_cast; ring)
