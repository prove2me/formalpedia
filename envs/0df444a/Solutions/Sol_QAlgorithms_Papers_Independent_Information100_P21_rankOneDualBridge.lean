-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.rankOneDualBridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:45:04.061453+00:00
-- url     : https://prove2.me/submissions/83223351-7c50-44ac-aa72-7d0110781496

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6RankOneBridge

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21

lemma rank_one_factor {ι : Type*} [Fintype ι] (W : Matrix ι ι ℂ) (hW : W.PosSemidef)
    (hr : W.rank = 1) : ∃ w : ι → ℂ, ∀ a b, W a b = w a * conj (w b) := by
  unfold Matrix.rank at hr
  obtain ⟨u, hu0, hu⟩ := finrank_eq_one_iff'.mp hr
  have col : ∀ k, ∃ c : ℂ, ∀ i, W i k = c * (u : ι → ℂ) i := by
    intro k
    obtain ⟨c, hc⟩ := hu ⟨W.mulVecLin (Pi.single k 1), LinearMap.mem_range_self _ _⟩
    refine ⟨c, fun i => ?_⟩
    have := congrArg (fun x : LinearMap.range W.mulVecLin => (x : ι → ℂ) i) hc
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose c hc using col
  have cross : ∀ i j k, W i k * W j j = W i j * W j k := by
    intro i j k; rw [hc, hc, hc, hc]; ring
  obtain ⟨j, hj⟩ : ∃ j, W j j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have ht : W.trace = 0 := by simp [Matrix.trace, hcon]
    rw [hW.trace_eq_zero_iff] at ht
    have h0 : (0 : Matrix ι ι ℂ).mulVecLin = 0 := by ext; simp
    rw [ht, h0, LinearMap.range_zero, finrank_bot] at hr
    exact zero_ne_one hr
  have hd := hW.diag_nonneg (i := j)
  rw [Complex.nonneg_iff] at hd
  set d := (W j j).re
  have hdj : W j j = (d : ℂ) := Complex.ext rfl (by simp [hd.2])
  have hdpos : 0 < d := by
    rcases hd.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hj; rw [hdj, ← h]; simp
  refine ⟨fun i => W i j / (Real.sqrt d : ℂ), fun a b => ?_⟩
  have hherm : conj (W b j) = W j b := by
    have := hW.isHermitian.apply j b; simpa using this
  have hsq : (Real.sqrt d : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hdpos.le]
  have hs0 : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hdpos).ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  simp only [map_div₀, Complex.conj_ofReal, hherm]
  have := cross a j b
  rw [hdj] at this
  field_simp
  rw [hsq, this]

lemma re_conj_mul_le (a b : ℂ) :
    (conj a * b).re ≤ (Complex.normSq a + Complex.normSq b) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]

end X6RankOneBridge

open X6RankOneBridge in
open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (W P Q : Op QQ) (hf : dualS W P Q) (hr : Matrix.rank W=1) : dualG W := by
  obtain ⟨hW, hP, hQ, hE⟩ := hf
  refine ⟨hW, ?_⟩
  obtain ⟨w, hw⟩ := rank_one_factor W hW hr
  have hWv : ∀ x : QQ → ℂ, W *ᵥ x = (star w ⬝ᵥ x) • w := by
    intro x; ext a
    simp only [Matrix.mulVec, dotProduct, hw, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
      RCLike.star_def, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- product bound: the 2x2 matrix (w (k,j)) is a contraction
  have bound : ∀ g : Fin 2 → ℂ, ∑ k, Complex.normSq (∑ j, w (k, j) * g j) ≤
      ∑ j, Complex.normSq (g j) := by
    intro g
    set e : Fin 2 → ℂ := fun k => ∑ j, w (k, j) * g j with he
    set N := ∑ k, Complex.normSq (e k)
    set G := ∑ j, Complex.normSq (g j)
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
    set x : QQ → ℂ := fun p => e p.1 * conj (g p.2) with hx
    set x' : QQ → ℂ := fun p => e p.1 * g p.2 with hx'
    have h1 : star x ⬝ᵥ w = (N : ℂ) := by
      simp only [N, x, e, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
        RCLike.star_def, map_mul, Complex.conj_conj, Complex.ofReal_add,
        ← Complex.mul_conj]
      ring
    have h2 : star w ⬝ᵥ x = (N : ℂ) := by
      have : star w ⬝ᵥ x = conj (star x ⬝ᵥ w) := by
        simp [dotProduct, map_sum, mul_comm]
      rw [this, h1, Complex.conj_ofReal]
    have h3 : star x ⬝ᵥ x = ((N * G : ℝ) : ℂ) := by
      simp only [N, G, x, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
        RCLike.star_def, map_mul, Complex.conj_conj, Complex.ofReal_add, Complex.ofReal_mul,
        ← Complex.mul_conj]
      ring
    have h4 : star x ⬝ᵥ (pt Q *ᵥ x) = star x' ⬝ᵥ (Q *ᵥ x') := by
      simp only [x, x', pt, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
        Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_conj]
      ring
    have key : star x ⬝ᵥ ((1 - W) *ᵥ x) =
        star x ⬝ᵥ (P *ᵥ x) + star x' ⬝ᵥ (Q *ᵥ x') := by
      rw [hE, Matrix.add_mulVec, dotProduct_add, h4]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hWv, dotProduct_smul, h1, h2,
      h3, smul_eq_mul] at key
    have hnn : 0 ≤ star x ⬝ᵥ (P *ᵥ x) + star x' ⬝ᵥ (Q *ᵥ x') :=
      add_nonneg (hP.dotProduct_mulVec_nonneg x) (hQ.dotProduct_mulVec_nonneg x')
    rw [← key] at hnn
    have hreal : 0 ≤ N * G - N * N := by
      have : ((N * G : ℝ) : ℂ) - (N : ℂ) * (N : ℂ) = ((N * G - N * N : ℝ) : ℂ) := by push_cast; ring
      rw [this] at hnn
      exact_mod_cast hnn
    rcases hN0.lt_or_eq with hpos | hzero
    · nlinarith
    · rw [← hzero]
      exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  -- hermiticity
  have herm : (1 - pt W).IsHermitian := by
    refine Matrix.IsHermitian.sub Matrix.isHermitian_one ?_
    ext p q
    simp only [Matrix.conjTranspose_apply, pt, hw, star_mul', RCLike.star_def,
      Complex.conj_conj]
    ring
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun v => ?_
  set Z : Fin 2 → Fin 2 → ℂ := fun i k => ∑ j, w (k, j) * v (i, j) with hZ
  have hval : star v ⬝ᵥ ((1 - pt W) *ᵥ v) =
      ∑ i, ∑ j, ((Complex.normSq (v (i, j)) : ℝ) : ℂ) - ∑ i, ∑ k, conj (Z i k) * Z k i := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    congr 1
    · simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, RCLike.star_def,
        ← Complex.mul_conj, mul_comm]
    · simp only [Z, dotProduct, Matrix.mulVec, pt, hw, Fintype.sum_prod_type, Fin.sum_univ_two,
        Pi.star_apply, RCLike.star_def, map_mul, map_add, Complex.conj_conj]
      ring
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [hval]
    simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re]
    have hb : ∑ i, ∑ k, (conj (Z i k) * Z k i).re ≤ ∑ i, ∑ k, Complex.normSq (Z i k) := by
      calc ∑ i, ∑ k, (conj (Z i k) * Z k i).re
          ≤ ∑ i, ∑ k, (Complex.normSq (Z i k) + Complex.normSq (Z k i)) / 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => re_conj_mul_le _ _
        _ = ∑ i, ∑ k, Complex.normSq (Z i k) := by
            simp only [Fin.sum_univ_two]; ring
    have hc : ∑ i, ∑ k, Complex.normSq (Z i k) ≤ ∑ i, ∑ j, Complex.normSq (v (i, j)) :=
      Finset.sum_le_sum fun i _ => bound (fun j => v (i, j))
    linarith
  · have := herm.im_star_dotProduct_mulVec_self v
    simp only [RCLike.im_to_complex] at this
    exact this.symm
