-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.entanglementFidelity_inputContinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:11:15.899871+00:00
-- url     : https://prove2.me/submissions/21200284-2eb2-4278-9bdc-feee5be056e7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology

/-- sesquilinear form underlying `fe` -/
def X7C_S {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (A : Superop I I) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, X j i * conj (Y l k) * A (Matrix.single j l 1) i k

lemma X7C_fe_eq {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (A : Superop I I) : fe X A = (X7C_S X X A).re := rfl

lemma X7C_quad {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (A : Superop I I) (t : ℝ) :
    X7C_S ((t : ℂ) • X + Y) ((t : ℂ) • X + Y) A
      = ((t * t : ℝ) : ℂ) * X7C_S X X A + (t : ℂ) * (X7C_S X Y A + X7C_S Y X A)
        + X7C_S Y Y A := by
  unfold X7C_S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, Complex.conj_ofReal]
  push_cast
  ring

lemma X7C_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (A : Superop I I) (hA : FiniteCPMap A) : 0 ≤ (X7C_S D D A).re := by
  obtain ⟨L, hL, hCP⟩ := hA
  set r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let v : Fin r × I → ℂ := fun p => if p.1 = e p.2 then 1 else 0
  have hX : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hM := hCP r _ hX
  let w : Fin r × I → ℂ := fun p => star (D (e.symm p.1) p.2)
  have h := hM.dotProduct_mulVec_nonneg w
  have hblock : ∀ a b : Fin r, (Matrix.of fun i i' =>
      Matrix.vecMulVec v (star v) (a, i) (b, i')) = Matrix.single (e.symm a) (e.symm b) 1 := by
    intro a b
    ext i i'
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, v, Pi.star_apply, Matrix.single_apply,
      Equiv.symm_apply_eq]
    split_ifs <;> simp_all
  have key : star w ⬝ᵥ ((QAlgorithms.idTensorSuperop L (Matrix.vecMulVec v (star v))) *ᵥ w)
      = X7C_S D D A := by
    simp only [dotProduct, Matrix.mulVec, QAlgorithms.idTensorSuperop, Matrix.of_apply, hblock,
      hL, w, Pi.star_apply, star_star, Fintype.sum_prod_type, Finset.mul_sum]
    have hs : ∀ f : I → ℂ, ∑ a : Fin r, f (e.symm a) = ∑ j, f j := fun f => e.symm.sum_comp f
    rw [hs (fun j => ∑ x_1, ∑ x_2 : Fin r, ∑ x_3,
      D j x_1 * (A (Matrix.single j (e.symm x_2) 1) x_1 x_3 * star (D (e.symm x_2) x_3)))]
    unfold X7C_S
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs (fun l => D j i * (A (Matrix.single j l 1) i k * star (D l k)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [RCLike.star_def]
    ring
  rw [key] at h
  exact (Complex.nonneg_iff.1 h).1

/-- Cauchy–Schwarz for the cross term -/
lemma X7C_cross {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (A : Superop I I) (hA : FiniteCPMap A) :
    |(X7C_S X Y A + X7C_S Y X A).re|
      ≤ 2 * Real.sqrt (X7C_S X X A).re * Real.sqrt (X7C_S Y Y A).re := by
  have hq : ∀ t : ℝ, 0 ≤ (X7C_S X X A).re * (t * t) + (X7C_S X Y A + X7C_S Y X A).re * t
      + (X7C_S Y Y A).re := by
    intro t
    have h1 := X7C_nonneg ((t : ℂ) • X + Y) A hA
    rw [X7C_quad] at h1
    simp only [Complex.add_re, Complex.re_ofReal_mul] at h1 ⊢
    linarith
  have ha : 0 ≤ (X7C_S X X A).re := X7C_nonneg X A hA
  have hc : 0 ≤ (X7C_S Y Y A).re := X7C_nonneg Y A hA
  generalize (X7C_S X X A).re = a at *
  generalize (X7C_S X Y A + X7C_S Y X A).re = b at *
  generalize (X7C_S Y Y A).re = c at *
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hsq : b ^ 2 ≤ (2 * Real.sqrt a * Real.sqrt c) ^ 2 := by
    have : (2 * Real.sqrt a * Real.sqrt c) ^ 2 = 4 * a * c := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hc]; ring
    rw [this]; linarith
  exact abs_le_of_sq_le_sq' hsq (by positivity) |> fun h => abs_le.2 h

open scoped MatrixOrder in
lemma X7C_g_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

open scoped MatrixOrder in
lemma X7C_g_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

open scoped MatrixOrder in
lemma X7C_g_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

open scoped MatrixOrder in
lemma X7C_g_le_trace {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    (hS : S.PosSemidef) : (((S.trace.re : ℝ) : ℂ) • (1 : Matrix n n ℂ) - S).PosSemidef := by
  have hsa : IsSelfAdjoint S := hS.1.isSelfAdjoint
  have key : S ≤ algebraMap ℝ (Matrix n n ℂ) S.trace.re := by
    rw [le_algebraMap_iff_spectrum_le]
    intro x hx
    rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hS.1.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef, Algebra.algebraMap_eq_smul_one] at key
  rw [show ((S.trace.re:ℂ) • (1:Matrix n n ℂ)) = S.trace.re • (1 : Matrix n n ℂ) from by
    ext i j; simp [Complex.real_smul]]
  exact key


abbrev X7C_q {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (A : Superop I I) : ℝ :=
  Real.sqrt (X7C_S X X A).re

lemma X7C_q_add {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (A : Superop I I) (hA : FiniteCPMap A) :
    X7C_q (X + Y) A ≤ X7C_q X A + X7C_q Y A := by
  have h := X7C_quad X Y A 1
  simp only [Complex.ofReal_one, one_smul, mul_one, one_mul] at h
  have hc := X7C_cross X Y A hA
  have ha := X7C_nonneg X A hA
  have hb := X7C_nonneg Y A hA
  unfold X7C_q
  rw [h]
  have hnn : 0 ≤ Real.sqrt (X7C_S X X A).re + Real.sqrt (X7C_S Y Y A).re := by positivity
  refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq hnn)
  simp only [Complex.add_re] at hc ⊢
  rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have := (abs_le.1 hc).2
  linarith

lemma X7C_q_neg {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (A : Superop I I) : X7C_q (-X) A = X7C_q X A := by
  unfold X7C_q X7C_S
  simp only [Matrix.neg_apply, map_neg, neg_mul_neg]

lemma X7C_q_zero {I : Type*} [Fintype I] [DecidableEq I]
    (A : Superop I I) : X7C_q (0 : Matrix I I ℂ) A = 0 := by
  simp [X7C_q, X7C_S]

lemma X7C_pos {I : Type*} [Fintype I] [DecidableEq I]
    (A : Superop I I) (hA : FiniteCPMap A) (X : Matrix I I ℂ) (hX : X.PosSemidef) :
    (A X).PosSemidef := by
  obtain ⟨L, hL, hCP⟩ := hA
  have h1 := hCP 1 (X.submatrix Prod.snd Prod.snd) (hX.submatrix _)
  have h2 := h1.submatrix (fun i : I => ((0 : Fin 1), i))
  convert h2 using 1
  ext i k
  simp [QAlgorithms.idTensorSuperop, ← hL]
  rfl

lemma X7C_rank1_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Superop I I) (hA : FiniteCPMap A) (v : I → ℂ) :
    X7C_S (Matrix.vecMulVec v (star v)) (Matrix.vecMulVec v (star v)) A
      = star v ⬝ᵥ (A (Matrix.vecMulVec v (star v)) *ᵥ v) := by
  obtain ⟨L, hL, -⟩ := hA
  have hY : A (Matrix.vecMulVec v (star v))
      = ∑ j, ∑ l, (v j * star (v l)) • A (Matrix.single j l 1) := by
    rw [← hL]
    conv_lhs => rw [Matrix.matrix_eq_sum_single (Matrix.vecMulVec v (star v))]
    have : ∀ j l, Matrix.single j l (Matrix.vecMulVec v (star v) j l)
        = (v j * star (v l)) • (Matrix.single j l 1 : Matrix I I ℂ) := by
      intro j l
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rfl
    simp only [this, map_sum, map_smul]
    simp only [hL]
  rw [hY]
  unfold X7C_S
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.vecMulVec_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, RCLike.star_def, Complex.conj_conj]
  ring

lemma X7C_rank1_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : Superop I I) (hA : TraceNonincreasingCPMap A) (v : I → ℂ) :
    X7C_q (Matrix.vecMulVec v (star v)) A ≤ (Matrix.vecMulVec v (star v)).trace.re := by
  have hP := Matrix.posSemidef_vecMulVec_self_star v
  set Y := A (Matrix.vecMulVec v (star v))
  have hYp : Y.PosSemidef := X7C_pos A hA.1 _ hP
  have hYt : Y.trace.re ≤ (Matrix.vecMulVec v (star v)).trace.re := hA.2 _ hP
  have hn : (Matrix.vecMulVec v (star v)).trace.re = (star v ⬝ᵥ v).re := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
  have hn0 : 0 ≤ (star v ⬝ᵥ v).re := by
    rw [← hn]; exact (Complex.nonneg_iff.1 hP.trace_nonneg).1
  have h1 := (X7C_g_le_trace hYp).dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul] at h1
  have h2 := (Complex.nonneg_iff.1 h1).1
  simp only [Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h2
  have hY0 : 0 ≤ Y.trace.re := (Complex.nonneg_iff.1 hYp.trace_nonneg).1
  unfold X7C_q
  rw [X7C_rank1_eq A hA.1 v, Real.sqrt_le_left (by rw [hn]; exact hn0)]
  rw [hn] at hYt ⊢
  nlinarith

lemma X7C_psd_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : Superop I I) (hA : TraceNonincreasingCPMap A) (P : Matrix I I ℂ) (hP : P.PosSemidef) :
    X7C_q P A ≤ P.trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hP
  refine (Finset.le_sum_of_subadditive (fun X => X7C_q X A) (X7C_q_zero A).le
    (fun X Y => X7C_q_add X Y A hA.1) _ _).trans ?_
  rw [Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun i _ => X7C_rank1_le A hA (v i)

lemma X7C_herm_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : Superop I I) (hA : TraceNonincreasingCPMap A) (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    X7C_q X A ≤ traceNorm X := by
  rw [X7C_g_traceNorm_herm hX]
  have hP := X7C_g_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hN := X7C_g_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  conv_lhs => rw [← X7C_g_parts X hX, sub_eq_add_neg]
  refine (X7C_q_add _ _ A hA.1).trans ?_
  rw [X7C_q_neg]
  exact add_le_add (X7C_psd_le A hA _ hP) (X7C_psd_le A hA _ hN)

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology
open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty I] (B Delta : Matrix I I ℂ) (hB : IsDensityMatrix B)
    (hBD : IsDensityMatrix (B + Delta)) (A : Superop I I) (hA : TraceNonincreasingCPMap A) :
    |fe (B + Delta) A - fe B A| ≤ traceNorm Delta ^ 2 + 2 * traceNorm Delta := by
  have hH : Delta.IsHermitian := by
    have := hBD.1.1.sub hB.1.1
    simpa using this
  have hq := X7C_herm_le A hA Delta hH
  have hqB : X7C_q B A ≤ 1 := by
    have := X7C_psd_le A hA B hB.1
    rw [hB.2] at this; simpa using this
  have hid := X7C_quad Delta B A 1
  simp only [Complex.ofReal_one, one_smul, mul_one, one_mul] at hid
  rw [X7C_fe_eq, X7C_fe_eq, add_comm B Delta, hid]
  have hc := X7C_cross Delta B A hA.1
  have hD0 := X7C_nonneg Delta A hA.1
  have hsq : (X7C_S Delta Delta A).re = X7C_q Delta A ^ 2 := (Real.sq_sqrt hD0).symm
  have hq0 : 0 ≤ X7C_q Delta A := Real.sqrt_nonneg _
  have hqB0 : 0 ≤ X7C_q B A := Real.sqrt_nonneg _
  simp only [Complex.add_re] at hc ⊢
  rw [show (X7C_S Delta Delta A).re + ((X7C_S Delta B A).re + (X7C_S B Delta A).re)
      + (X7C_S B B A).re - (X7C_S B B A).re
      = (X7C_S Delta Delta A).re + ((X7C_S Delta B A).re + (X7C_S B Delta A).re) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hD0, hsq]
  change _ ≤ 2 * X7C_q Delta A * X7C_q B A at hc
  have h1 : X7C_q Delta A ^ 2 ≤ traceNorm Delta ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have h2 : X7C_q Delta A * X7C_q B A ≤ traceNorm Delta * 1 :=
    mul_le_mul hq hqB hqB0 (hq0.trans hq)
  nlinarith

end
