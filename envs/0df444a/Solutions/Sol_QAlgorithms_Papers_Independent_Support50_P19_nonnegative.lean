-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P19.nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:59:57.630663+00:00
-- url     : https://prove2.me/submissions/3e73513a-86a0-44ea-9c4e-117972e0ddc7

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

section NN_helpers

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P09 (logExt)

lemma NN_real {ι κ : Type} [Fintype ι] [Fintype κ] (a q : ℝ) (hpq : a.HolderConjugate q)
    (lam : ι → ℝ) (p μ : κ → ℝ) (w : ι → κ → ℝ) (hl : ∀ i, 0 ≤ lam i) (hp : ∀ j, 0 ≤ p j)
    (hpμ : ∀ j, p j ^ q = μ j) (hμ : ∑ j, μ j = 1) (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (h1 : ∑ i, lam i * ∑ j, w i j * p j = 1) : 1 ≤ ∑ i, lam i ^ a := by
  have hq1 : 1 ≤ q := hpq.symm.lt.le
  have hc0 : ∀ i, 0 ≤ ∑ j, w i j * p j := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (hp j)
  have hc : ∀ i, (∑ j, w i j * p j) ^ q ≤ ∑ j, w i j * μ j := by
    intro i
    have := (convexOn_rpow hq1).map_sum_le (t := Finset.univ) (w := w i) (p := p)
      (fun j _ => hw i j) (hrow i) (fun j _ => Set.mem_Ici.2 (hp j))
    simpa [smul_eq_mul, hpμ] using this
  have hsum : ∑ i, (∑ j, w i j * p j) ^ q ≤ 1 := by
    calc ∑ i, (∑ j, w i j * p j) ^ q ≤ ∑ i, ∑ j, w i j * μ j := Finset.sum_le_sum fun i _ => hc i
      _ = ∑ j, μ j * ∑ i, w i j := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 1 := by simp [hcol, hμ]
  have hy : ∀ i, lam i * (∑ j, w i j * p j) ≤
      lam i ^ a / a + (∑ j, w i j * p j) ^ q / q := fun i =>
    Real.young_inequality_of_nonneg (hl i) (hc0 i) hpq
  have h2 : 1 ≤ (∑ i, lam i ^ a) / a + (∑ i, (∑ j, w i j * p j) ^ q) / q := by
    rw [← h1, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hy i
  have ha := hpq.pos
  have hqp := hpq.symm.pos
  have hinv := hpq.inv_add_inv_eq_one
  have h3 : (∑ i, (∑ j, w i j * p j) ^ q) / q ≤ 1 / q := div_le_div_of_nonneg_right hsum hqp.le
  have h4 : 1 / a ≤ (∑ i, lam i ^ a) / a := by
    have : 1 / a + 1 / q = 1 := by simpa [one_div] using hinv
    linarith
  exact (div_le_div_iff_of_pos_right ha).1 h4
lemma NN_conj_mul {I : Type} [Fintype I] [DecidableEq I] (U A B : Matrix I I ℂ)
    (hU : star U * U = 1) :
    (U * A * star U) * (U * B * star U) = U * (A * B) * star U := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]

lemma NN_cfc_eq {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : cfc f A = (hA.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun j => ((f (hA.eigenvalues j) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix I I ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma NN_spec {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix I I ℂ) := by
  have := NN_cfc_eq hA id
  rw [cfc_id ℝ A] at this
  simpa using this

lemma NN_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

/-- trace of `D_p W D_l W*`. -/
lemma NN_trace_expand {I : Type} [Fintype I] [DecidableEq I] (p l : I → ℝ) (W : Matrix I I ℂ) :
    (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * W * Matrix.diagonal (fun j => ((l j : ℝ) : ℂ))
      * star W).trace.re = ∑ i, l i * ∑ j, Complex.normSq (W j i) * p j := by
  have hM : Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * W *
      Matrix.diagonal (fun j => ((l j : ℝ) : ℂ)) = Matrix.of fun j i => (p j : ℂ) * W j i * l i := by
    ext j i; simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hM]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ((p j : ℂ) * W j i * (l i : ℂ) * star (W j i)) =
      ((l i * (Complex.normSq (W j i) * p j) : ℝ) : ℂ) := by
    rw [Complex.star_def]
    push_cast
    rw [← Complex.mul_conj]; ring
  rw [this, Complex.ofReal_re]

lemma NN_normSq_row {I : Type} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ)
    (h : star W * W = 1) (i : I) : ∑ j, Complex.normSq (W j i) = 1 := by
  have := congrArg (fun M => (M i i).re) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.re_sum,
    Complex.one_re] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma NN_normSq_col {I : Type} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ)
    (h : W * star W = 1) (j : I) : ∑ i, Complex.normSq (W j i) = 1 := by
  have := congrArg (fun M => (M j j).re) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.re_sum,
    Complex.one_re] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

lemma NN_main {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (ha : 1 < a)
    (ρ σ : Matrix I I ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (htρ : ρ.trace = 1)
    (htσ : σ.trace = 1) (hsup : SupportIncluded ρ σ) :
    1 ≤ (supportPower (supportPower σ ((1-a)/(2*a)) * ρ * supportPower σ ((1-a)/(2*a)))
      a).trace.re := by
  have hs : σ.IsHermitian := hσ.1
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  set U : Matrix I I ℂ := (hs.eigenvectorUnitary : Matrix I I ℂ) with hUdef
  set μ := hs.eigenvalues with hμdef
  have hU1 : star U * U = 1 := Unitary.star_mul_self_of_mem hs.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Unitary.mul_star_self_of_mem hs.eigenvectorUnitary.2
  have hμ0 : ∀ j, 0 ≤ μ j := hσ.eigenvalues_nonneg
  set fs : ℝ → ℝ := fun x => if x = 0 then 0 else Real.rpow x ((1-a)/(2*a)) with hfs
  set fp : ℝ → ℝ := fun x => if x = 0 then 0 else x ^ ((a-1)/a) with hfp
  set fπ : ℝ → ℝ := fun x => if x = 0 then 0 else 1 with hfπ
  have hS : supportPower σ ((1-a)/(2*a)) =
      U * Matrix.diagonal (fun j => ((fs (μ j) : ℝ) : ℂ)) * star U := NN_cfc_eq hs _
  set S := supportPower σ ((1-a)/(2*a)) with hSdef
  set P := U * Matrix.diagonal (fun j => ((fp (μ j) : ℝ) : ℂ)) * star U with hP
  set Pr := U * Matrix.diagonal (fun j => ((fπ (μ j) : ℝ) : ℂ)) * star U with hPrd
  have hSPS : S * P * S = Pr := by
    rw [hS, NN_conj_mul _ _ _ hU1, NN_conj_mul _ _ _ hU1, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    refine congrArg (fun d => U * Matrix.diagonal d * star U) (funext fun j => ?_)
    by_cases h : μ j = 0
    · simp [hfs, hfp, hfπ, h]
    · have hp : 0 < μ j := lt_of_le_of_ne (hμ0 j) (Ne.symm h)
      simp only [hfs, hfp, hfπ, h, if_false]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      rw [Real.rpow_eq_pow, ← Real.rpow_add hp, ← Real.rpow_add hp]
      have : (1 - a) / (2 * a) + (a - 1) / a + (1 - a) / (2 * a) = 0 := by
        field_simp; ring
      rw [this, Real.rpow_zero]
  have hσeq : σ = U * Matrix.diagonal (fun j => ((μ j : ℝ) : ℂ)) * star U := NN_spec hs
  have hσPr : σ * Pr = σ := by
    calc σ * Pr = (U * Matrix.diagonal (fun j => ((μ j : ℝ) : ℂ)) * star U) * Pr :=
          congrArg (· * Pr) hσeq
      _ = σ := by
          rw [hPrd, NN_conj_mul _ _ _ hU1, Matrix.diagonal_mul_diagonal, hσeq]
          refine congrArg (fun d => U * Matrix.diagonal d * star U) (funext fun j => ?_)
          by_cases h : μ j = 0 <;> simp [hfπ, h]
  have hz : σ * (1 - Pr) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hσPr, sub_self]
  have hρz : ρ * (1 - Pr) = 0 := by
    ext i j
    have hv : (1 - Pr) *ᵥ (Pi.single j 1) ∈ LinearMap.ker σ.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
    have h2 := hsup hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at h2
    have h3 := congrFun h2 i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3
  have hρPr : ρ * Pr = ρ := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hρz
    exact hρz.symm
  have hSa : Sᴴ = S := (cfc_predicate _ σ : IsSelfAdjoint S)
  set X := S * ρ * S with hXdef
  have htrPX : (P * X).trace = 1 := by
    rw [hXdef, show P * (S * ρ * S) = (P * S * ρ) * S by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show S * (P * S * ρ) = S * P * S * ρ by simp only [Matrix.mul_assoc],
      hSPS, Matrix.trace_mul_comm, hρPr, htρ]
  have hXpsd : X.PosSemidef := by
    have := hρ.conjTranspose_mul_mul_same S
    rwa [hSa] at this
  have hX : X.IsHermitian := hXpsd.1
  set V : Matrix I I ℂ := (hX.eigenvectorUnitary : Matrix I I ℂ) with hVdef
  set l := hX.eigenvalues with hldef
  have hV1 : star V * V = 1 := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have hV2 : V * star V = 1 := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  have hl0 : ∀ i, 0 ≤ l i := hXpsd.eigenvalues_nonneg
  have hXeq : X = V * Matrix.diagonal (fun j => ((l j : ℝ) : ℂ)) * star V := NN_spec hX
  set W := star U * V with hW
  have htr2 : (P * X).trace = (Matrix.diagonal (fun j => ((fp (μ j) : ℝ) : ℂ)) * W *
      Matrix.diagonal (fun j => ((l j : ℝ) : ℂ)) * star W).trace := by
    rw [show P * X = U * (Matrix.diagonal (fun j => ((fp (μ j) : ℝ) : ℂ)) * star U * V *
      Matrix.diagonal (fun j => ((l j : ℝ) : ℂ)) * star V) by
        rw [hXeq, hP]; simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [hW, StarMul.star_mul, star_star, Matrix.mul_assoc]
  have h1 : ∑ i, l i * ∑ j, Complex.normSq (W j i) * fp (μ j) = 1 := by
    rw [← NN_trace_expand, ← htr2, htrPX, Complex.one_re]
  have hWW1 : star W * W = 1 := by
    rw [hW, StarMul.star_mul, star_star]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hV1]
  have hWW2 : W * star W = 1 := by
    rw [hW, StarMul.star_mul, star_star]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV2, Matrix.mul_one, hU1]
  have hμsum : ∑ j, μ j = 1 := by
    have := hs.trace_eq_sum_eigenvalues
    rw [htσ] at this
    have h' := congrArg Complex.re this
    simpa [Complex.re_sum] using h'.symm
  have hpq := Real.HolderConjugate.conjExponent ha
  have hpμ : ∀ j, fp (μ j) ^ (Real.conjExponent a) = μ j := by
    intro j
    by_cases h : μ j = 0
    · simp only [hfp, h, if_true]
      exact Real.zero_rpow hpq.symm.ne_zero
    · simp only [hfp, h, if_false]
      rw [← Real.rpow_mul (hμ0 j), Real.conjExponent]
      have : (a - 1) / a * (a / (a - 1)) = 1 := by field_simp
      rw [this, Real.rpow_one]
  have hfp0 : ∀ j, 0 ≤ fp (μ j) := by
    intro j; simp only [hfp]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (hμ0 j) _
  have key := NN_real a _ hpq l (fun j => fp (μ j)) μ (fun i j => Complex.normSq (W j i)) hl0
    hfp0 hpμ hμsum (fun i j => Complex.normSq_nonneg _) (NN_normSq_row W hWW1)
    (NN_normSq_col W hWW2) h1
  have htrX : (supportPower X a).trace.re = ∑ i, l i ^ a := by
    rw [supportPower, NN_cfc_trace hX, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_re]
    split_ifs with h
    · rw [show l i = 0 from h, Real.zero_rpow ha0.ne']
    · rfl
  rw [htrX]; exact key

lemma NN_ereal (a T : ℝ) (ha : 1 < a) (hT : 1 ≤ T) :
    0 ≤ ((1 / (a-1) : ℝ) : EReal) * logExt ((T : ℝ) : EReal) := by
  have hl : logExt ((T : ℝ) : EReal) = ((Real.logb 2 T : ℝ) : EReal) := by
    rw [logExt, if_neg (EReal.coe_ne_top T), if_neg (by
      rw [EReal.coe_nonpos]; linarith), EReal.toReal_coe]
  rw [hl, ← EReal.coe_mul, EReal.coe_nonneg]
  have : 0 < a - 1 := by linarith
  exact mul_nonneg (by positivity) (Real.logb_nonneg (by norm_num) hT)

end NN_helpers

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

/-- PDF p.14, Corollary 7: nonnegativity for normalized states, only the proved order range. -/
theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (a : ℝ) (ha : 1 < a)
    (ha2 : a ≤ 2) (rho sigma : {X : Matrix I I ℂ // IsDensityMatrix X}) :
    0 ≤ sandwichedD a rho.1 sigma.1 := by
  simp only [sandwichedD]
  split_ifs with h
  · exact le_top
  · have hsup : QAlgorithms.Papers.Independent.Information100.P71.SupportIncluded rho.1 sigma.1 := by
      by_contra hc; exact h ⟨ha, hc⟩
    exact NN_ereal a _ ha (NN_main a ha rho.1 sigma.1 rho.2.1 sigma.2.1 rho.2.2 sigma.2.2 hsup)

end

