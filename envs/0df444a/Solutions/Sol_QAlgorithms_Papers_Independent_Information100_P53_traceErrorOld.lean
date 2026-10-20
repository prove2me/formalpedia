-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.traceErrorOld
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:21:13.041831+00:00
-- url     : https://prove2.me/submissions/ff48a0d5-b70d-47df-a4ab-21800e332db3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

noncomputable section


open scoped Matrix ComplexOrder MatrixOrder

lemma g53_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g53_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma g53_posPart_aux {n : Type} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma g53_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g53_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g53_posPart_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [g53_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := g53_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact g53_posPart_aux lam hA hB hu hD

lemma g53_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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


lemma g53h_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma g53h_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← g53h_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma g53h_tr_le_traceNorm {n : Type} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [g53_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := g53_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := g53_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (g53_parts Y hY).symm
  have a1 := g53h_tr_psd_mul h1 hP
  have a2 := g53h_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

lemma g53h_helstrom {n : Type} [Fintype n] [DecidableEq n] {A B E F : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hE : E.PosSemidef) (hF : F.PosSemidef)
    (hEF : (1 - E - F).PosSemidef) (hAB : (A + B).PosSemidef) :
    (E * A).trace.re + (F * B).trace.re ≤
      ((A.trace.re + B.trace.re) + QAlgorithms.traceNorm (A - B)) / 2 := by
  have k1 := g53h_tr_psd_mul hEF hAB
  have hX1 : (1 - (E - F)).PosSemidef := by
    have : 1 - (E - F) = (1 - E - F) + (2 : ℂ) • F := by
      rw [two_smul]; abel
    rw [this]; exact hEF.add (hF.smul (by norm_num))
  have hX2 : (1 + (E - F)).PosSemidef := by
    have : 1 + (E - F) = (1 - E - F) + (2 : ℂ) • E := by
      rw [two_smul]; abel
    rw [this]; exact hEF.add (hE.smul (by norm_num))
  have k2 := g53h_tr_le_traceNorm (hA.sub hB) hX1 hX2
  have eq1 : (E * A).trace.re + (F * B).trace.re =
      ((E + F) * (A + B)).trace.re / 2 + ((E - F) * (A - B)).trace.re / 2 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_add,
      Matrix.trace_sub, Complex.add_re, Complex.sub_re]
    ring
  have eq2 : ((1 - E - F) * (A + B)).trace.re =
      (A.trace.re + B.trace.re) - ((E + F) * (A + B)).trace.re := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_sub, Complex.add_re, Complex.sub_re]
    ring
  rw [eq1]; linarith

lemma g53h_pair_sum {M : ℕ} (f : Fin M → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (f i + f j) = ((M : ℝ) - 1) * ∑ i, f i := by
  simp only [Finset.sum_filter]
  have h1 : ∀ i j : Fin M, (if i < j then f i + f j else 0) =
      (if i < j then f i else 0) + (if i < j then f j else 0) := by
    intro i j; split_ifs <;> simp
  simp only [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j else 0)]
  rw [← Finset.sum_add_distrib]
  have h2 : ∀ i : Fin M, (∑ j, if i < j then f i else 0) + (∑ j, if j < i then f i else 0) =
      ((M : ℝ) - 1) * f i := by
    intro i
    rw [← Finset.sum_add_distrib]
    have h3 : ∀ j : Fin M, ((if i < j then f i else 0) + (if j < i then f i else 0)) =
        f i - (if j = i then f i else 0) := by
      intro j
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_gt h, not_lt.2 h.le]
      · subst h; simp
      · simp [h, ne_of_lt h, not_lt.2 h.le]
    simp only [h3, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul]
    ring
  simp only [h2, ← Finset.mul_sum]

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder

open Finset

/-- PDF p.3, Theorem 1 ([7, Theorem 1], Qiu): fixed-prior trace-norm
lower bound on optimized discrimination error. M>=2 is required by M-1.
This is a cited background result; traceNorm has no factor one half. -/
theorem solution {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    1 / 2 - traceSum p rho / (2 * ((M : ℝ) - 1)) ≤ 1 - mixedOptSuccess p rho := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have i0 : Fin M := ⟨0, by omega⟩
  haveI : Nonempty {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D} := by
    refine ⟨⟨fun i => if i = i0 then 1 else 0, ?_, ?_⟩⟩
    · intro i; show (if i = i0 then (1 : Matrix (Fin N) (Fin N) ℂ) else 0).PosSemidef; split_ifs
      · exact Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · simp
  have key : ∀ D : Fin M → Matrix (Fin N) (Fin N) ℂ, IsPOVM D →
      ∑ j, p j * effectProb (D j) (rho j) ≤ 1 / 2 + traceSum p rho / (2 * ((M : ℝ) - 1)) := by
    intro D hD
    set s : Fin M → ℝ := fun j => p j * effectProb (D j) (rho j) with hs
    have hpsd : ∀ i, ((p i : ℂ) • rho i).PosSemidef := fun i =>
      (hrho i).1.smul (by exact_mod_cast (hp.1 i))
    have htr : ∀ i, ((p i : ℂ) • rho i).trace.re = p i := by
      intro i; rw [Matrix.trace_smul, (hrho i).2]; simp
    have hEA : ∀ i, (D i * ((p i : ℂ) • rho i)).trace.re = s i := by
      intro i; simp only [hs, effectProb, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Complex.re_ofReal_mul]
    have hpair : ∀ i j, i ≠ j → s i + s j ≤
        ((p i + p j) + traceNorm ((p i : ℂ) • rho i - (p j : ℂ) • rho j)) / 2 := by
      intro i j hij
      have hrest : (1 - D i - D j).PosSemidef := by
        have hsum := hD.2
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩)] at hsum
        have : 1 - D i - D j = ∑ k ∈ (Finset.univ.erase i).erase j, D k := by
          rw [← hsum]; abel
        rw [this]
        exact Matrix.posSemidef_sum _ (fun k _ => hD.1 k)
      have := g53h_helstrom (hpsd i).1 (hpsd j).1 (hD.1 i) (hD.1 j) hrest ((hpsd i).add (hpsd j))
      rw [hEA, hEA, htr, htr] at this
      exact this
    have hsum_le : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (s i + s j) ≤
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (((p i + p j) + traceNorm ((p i : ℂ) • rho i - (p j : ℂ) • rho j)) / 2) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j hj
      exact hpair i j (ne_of_lt (Finset.mem_filter.1 hj).2)
    rw [g53h_pair_sum] at hsum_le
    have hsplit : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (((p i + p j) + traceNorm ((p i : ℂ) • rho i - (p j : ℂ) • rho j)) / 2) =
        (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (p i + p j)) / 2 + traceSum p rho / 2 := by
      simp only [traceSum, pairSum, add_div, Finset.sum_add_distrib, Finset.sum_div]
    rw [hsplit, g53h_pair_sum, hp.2] at hsum_le
    show ∑ j, s j ≤ _
    rw [show 1 / 2 + traceSum p rho / (2 * ((M : ℝ) - 1)) =
      (((M : ℝ) - 1) * 1 / 2 + traceSum p rho / 2) / ((M : ℝ) - 1) by field_simp]
    rw [le_div_iff₀ hM1]; linarith
  unfold mixedOptSuccess
  have : (⨆ D : {D : Fin M → Matrix (Fin N) (Fin N) ℂ // IsPOVM D},
      ∑ j, p j * effectProb (D.1 j) (rho j)) ≤ 1 / 2 + traceSum p rho / (2 * ((M : ℝ) - 1)) :=
    ciSup_le (fun D => key D.1 D.2)
  linarith



end

