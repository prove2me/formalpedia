-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.productOverlapSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:59:09.205917+00:00
-- url     : https://prove2.me/submissions/123c99bc-a1cb-4db3-8ee7-6f1b13a0091d

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6POS

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21

lemma orth_coord {u : Fin 2 → Vec (Fin 2)} (hu : Orthonormal ℂ u) (m n : Fin 2) :
    u n 0 * conj (u m 0) + u n 1 * conj (u m 1) = if m = n then 1 else 0 := by
  have h := orthonormal_iff_ite.mp hu m n
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct, Fin.sum_univ_two] using h

end X6POS

open X6POS in
open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (b : Vec QQ) (hb : ‖b‖=1) (a1 a2 : ℝ)
  (u f : Fin 2 → Vec (Fin 2)) (hs : schmidt b a1 a2 u f) :
  IsGreatest {q : ℝ | ∃ p : Vec QQ, unitProduct p ∧ q=Complex.normSq (inner ℂ p b)} (a1^2) ∧
  (pt (proj b)).charpoly =
    (Polynomial.X-Polynomial.C ((a1^2:ℝ):ℂ)) *
    (Polynomial.X-Polynomial.C ((a2^2:ℝ):ℂ)) *
    (Polynomial.X-Polynomial.C ((a1*a2:ℝ):ℂ)) *
    (Polynomial.X-Polynomial.C ((-a1*a2:ℝ):ℂ)) ∧
  IsGreatest {q : ℝ | ∃ v : QQ → ℂ, v≠0 ∧ (pt (proj b)).mulVec v = (q:ℂ) • v} (a1^2) := by
  obtain ⟨hu, hf, ha2, ha21, hsq, hbeq⟩ := hs
  have ha1 : 0 ≤ a1 := ha2.trans ha21
  have hU := orth_coord hu
  have hF := orth_coord hf
  set α : Fin 2 → ℂ := ![(a1 : ℂ), (a2 : ℂ)] with hα
  have hbp : ∀ p : QQ, b p = (a1 : ℂ) * u 0 p.1 * f 0 p.2 + (a2 : ℂ) * u 1 p.1 * f 1 p.2 := by
    intro p
    rw [hbeq]
    simp [tensor, mul_assoc]
  set ptb := pt (proj b) with hptb
  have hpt : ∀ p q : QQ, ptb p q = b (p.1, q.2) * conj (b (q.1, p.2)) := fun _ _ => rfl
  -- partial contractions
  have step1 : ∀ i s, ∑ l, b (i, l) * conj (f s l) = α s * u s i := by
    intro i s
    simp only [Fin.sum_univ_two, hbp]
    have h00 := hF 0 0; have h01 := hF 0 1; have h10 := hF 1 0; have h11 := hF 1 1
    simp only [if_true, Fin.zero_eta, Fin.isValue, zero_ne_one, one_ne_zero, if_false] at h00 h01 h10 h11
    fin_cases s
    · simp only [hα, Fin.zero_eta, Matrix.cons_val_zero]
      linear_combination ((a1 : ℂ) * u 0 i) * h00 + ((a2 : ℂ) * u 1 i) * h01
    · simp only [hα, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination ((a1 : ℂ) * u 0 i) * h10 + ((a2 : ℂ) * u 1 i) * h11
  have step2 : ∀ j r, ∑ k, conj (b (k, j)) * u r k = α r * conj (f r j) := by
    intro j r
    simp only [Fin.sum_univ_two, hbp, map_add, map_mul, Complex.conj_ofReal]
    have h00 := hU 0 0; have h01 := hU 0 1; have h10 := hU 1 0; have h11 := hU 1 1
    simp only [if_true, Fin.zero_eta, Fin.isValue, zero_ne_one, one_ne_zero, if_false] at h00 h01 h10 h11
    fin_cases r
    · simp only [hα, Fin.zero_eta, Matrix.cons_val_zero]
      linear_combination ((a1 : ℂ) * conj (f 0 j)) * h00 + ((a2 : ℂ) * conj (f 1 j)) * h10
    · simp only [hα, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination ((a1 : ℂ) * conj (f 0 j)) * h01 + ((a2 : ℂ) * conj (f 1 j)) * h11
  -- eigenvectors
  set w : Fin 2 → Fin 2 → QQ → ℂ := fun r s p => u r p.1 * conj (f s p.2) with hw
  have eig : ∀ r s, ptb *ᵥ w r s = (α r * α s) • w s r := by
    intro r s
    ext ⟨i, j⟩
    have e : (ptb *ᵥ w r s) (i, j) =
        (∑ l, b (i, l) * conj (f s l)) * (∑ k, conj (b (k, j)) * u r k) := by
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, hpt, hw]
      ring
    rw [e, step1, step2]
    simp only [Pi.smul_apply, smul_eq_mul, hw]
    ring
  -- the unitary K
  set K : Matrix QQ QQ ℂ := Matrix.of fun p c => w c.1 c.2 p with hK
  have gram : ∀ c c' : QQ, ∑ p, conj (w c.1 c.2 p) * w c'.1 c'.2 p =
      (1 : Matrix QQ QQ ℂ) c c' := by
    rintro ⟨r, s⟩ ⟨r', s'⟩
    have e : ∑ p : QQ, conj (w r s p) * w r' s' p =
        (u r' 0 * conj (u r 0) + u r' 1 * conj (u r 1)) *
          (f s 0 * conj (f s' 0) + f s 1 * conj (f s' 1)) := by
      simp only [hw, Fintype.sum_prod_type, Fin.sum_univ_two, map_mul, Complex.conj_conj]; ring
    show ∑ p : QQ, conj (w r s p) * w r' s' p = _
    rw [e, hU r r', hF s' s]
    by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [h1, h2, eq_comm, Matrix.one_apply]
  have hKK : Kᴴ * K = 1 := by
    ext c c'
    rw [Matrix.mul_apply, ← gram c c']
    simp only [Matrix.conjTranspose_apply, hK, Matrix.of_apply, RCLike.star_def]
  have hKK' : K * Kᴴ = 1 := mul_eq_one_comm.mp hKK
  let Ku : (Matrix QQ QQ ℂ)ˣ := ⟨K, Kᴴ, hKK', hKK⟩
  set N : Matrix QQ QQ ℂ := Matrix.of fun c c' =>
    if c = (c'.2, c'.1) then α c'.1 * α c'.2 else 0 with hN
  have hPK : ptb * K = K * N := by
    ext p c'
    have l : (ptb * K) p c' = (ptb *ᵥ w c'.1 c'.2) p := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hK]
    rw [l, eig]
    simp [Matrix.mul_apply, hK, hN, mul_comm]
  set H : Matrix QQ QQ ℂ := Matrix.of fun q c =>
    if c = (0, 1) then (if q = (0, 1) then 1 else if q = (1, 0) then 1 else 0)
    else if c = (1, 0) then (if q = (0, 1) then 1 else if q = (1, 0) then -1 else 0)
    else if q = c then 1 else 0 with hH
  set H' : Matrix QQ QQ ℂ := Matrix.of fun c q =>
    if c = (0, 1) then (if q = (0, 1) then 1/2 else if q = (1, 0) then 1/2 else 0)
    else if c = (1, 0) then (if q = (0, 1) then 1/2 else if q = (1, 0) then -1/2 else 0)
    else if q = c then 1 else 0 with hH'
  have hHH : H * H' = 1 := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
      simp [hH, hH', Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.one_apply] <;> norm_num
  have hHH' : H' * H = 1 := mul_eq_one_comm.mp hHH
  let Hu : (Matrix QQ QQ ℂ)ˣ := ⟨H, H', hHH, hHH'⟩
  set dval : QQ → ℂ := fun c => if c = (0, 0) then ((a1^2:ℝ):ℂ) else if c = (1, 1) then
    ((a2^2:ℝ):ℂ) else if c = (0, 1) then ((a1*a2:ℝ):ℂ) else ((-a1*a2:ℝ):ℂ) with hdval
  have hNH : N * H = H * Matrix.diagonal dval := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
      simp [hN, hH, hdval, hα, Matrix.mul_apply, Matrix.mul_diagonal, Fintype.sum_prod_type,
        Fin.sum_univ_two] <;> ring
  let Gu := Ku * Hu
  have hGv : (Gu : Matrix QQ QQ ℂ) = K * H := rfl
  have hPG : ptb * Gu = Gu * Matrix.diagonal dval := by
    rw [hGv, ← Matrix.mul_assoc, hPK, Matrix.mul_assoc, hNH, Matrix.mul_assoc]
  have hsim : ptb = (Gu : Matrix QQ QQ ℂ) * Matrix.diagonal dval * (Gu : Matrix QQ QQ ℂ)⁻¹ := by
    rw [← hPG, Matrix.mul_assoc, ← Matrix.coe_units_inv, Units.mul_inv, Matrix.mul_one]
  have hchar : ptb.charpoly =
      (Polynomial.X-Polynomial.C ((a1^2:ℝ):ℂ)) *
      (Polynomial.X-Polynomial.C ((a2^2:ℝ):ℂ)) *
      (Polynomial.X-Polynomial.C ((a1*a2:ℝ):ℂ)) *
      (Polynomial.X-Polynomial.C ((-a1*a2:ℝ):ℂ)) := by
    rw [hsim, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal, Fintype.prod_prod_type,
      Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [hdval]
    simp
    ring
  -- product overlap
  have hpart1 : IsGreatest {q : ℝ | ∃ p : Vec QQ, unitProduct p ∧
      q = Complex.normSq (inner ℂ p b)} (a1^2) := by
    have h00 := hU 0 0; have h01 := hU 0 1
    have g00 := hF 0 0; have g01 := hF 0 1
    simp only [if_true, Fin.zero_eta, Fin.isValue, zero_ne_one, one_ne_zero, if_false]
      at h00 h01 g00 g01
    refine ⟨⟨tensor (u 0) (f 0), ⟨u 0, f 0, hu.1 0, hf.1 0, rfl⟩, ?_⟩, ?_⟩
    · have e : inner ℂ (tensor (u 0) (f 0)) b = (a1 : ℂ) := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
          Fin.sum_univ_two, tensor, hbp, Pi.star_apply, RCLike.star_def, map_mul,
          WithLp.ofLp_toLp]
        linear_combination ((a1 : ℂ) * (f 0 0 * conj (f 0 0) + f 0 1 * conj (f 0 1))) * h00 +
          (a1 : ℂ) * g00 + ((a2 : ℂ) * (f 1 0 * conj (f 0 0) + f 1 1 * conj (f 0 1))) * h01
      rw [e, Complex.normSq_ofReal, sq]
    · rintro q ⟨p, ⟨e, g, he, hg, rfl⟩, rfl⟩
      have hz : inner ℂ (tensor e g) b = conj ((a1 : ℂ) * inner ℂ (u 0) e * inner ℂ (f 0) g +
          (a2 : ℂ) * inner ℂ (u 1) e * inner ℂ (f 1) g) := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
          Fin.sum_univ_two, tensor, hbp, Pi.star_apply, RCLike.star_def, map_add, map_mul,
          Complex.conj_conj, Complex.conj_ofReal, WithLp.ofLp_toLp]
        ring
      have bu := hu.sum_inner_products_le (s := Finset.univ) (x := e)
      have bf := hf.sum_inner_products_le (s := Finset.univ) (x := g)
      rw [he] at bu; rw [hg] at bf
      simp only [Fin.sum_univ_two, one_pow] at bu bf
      set x0 := ‖inner ℂ (u 0) e‖; set x1 := ‖inner ℂ (u 1) e‖
      set y0 := ‖inner ℂ (f 0) g‖; set y1 := ‖inner ℂ (f 1) g‖
      have hx0 : 0 ≤ x0 := norm_nonneg _; have hx1 : 0 ≤ x1 := norm_nonneg _
      have hy0 : 0 ≤ y0 := norm_nonneg _; have hy1 : 0 ≤ y1 := norm_nonneg _
      have hn : ‖inner ℂ (tensor e g) b‖ ≤ a1 := by
        rw [hz, Complex.norm_conj]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg ha1, Real.norm_of_nonneg ha2]
        have hxy : x0 * y0 + x1 * y1 ≤ 1 := by
          nlinarith [sq_nonneg (x0 - y0), sq_nonneg (x1 - y1)]
        have : a2 * x1 * y1 ≤ a1 * x1 * y1 := by
          have := mul_nonneg hx1 hy1
          nlinarith
        nlinarith [mul_nonneg ha1 (mul_nonneg hx0 hy0)]
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  refine ⟨hpart1, hchar, ?_, ?_⟩
  · refine ⟨w 0 0, ?_, ?_⟩
    · intro h0
      have := gram (0, 0) (0, 0)
      simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at this
      exact zero_ne_one this
    · rw [eig]
      congr 1
      simp [hα]; push_cast; ring
  · rintro q ⟨v, hv0, hev⟩
    have hker : (Matrix.scalar QQ (q : ℂ) - ptb) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hev]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
    rw [← Matrix.eval_charpoly, hchar] at hdet
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      mul_eq_zero, sub_eq_zero] at hdet
    have hb1 : a1 * a2 ≤ a1 ^ 2 := by nlinarith
    have hb2 : a2 ^ 2 ≤ a1 ^ 2 := by nlinarith
    have hb3 : -a1 * a2 ≤ a1 ^ 2 := by nlinarith [mul_nonneg ha1 ha2]
    rcases hdet with ((h | h) | h) | h <;> have h' := Complex.ofReal_injective h <;>
      linarith
