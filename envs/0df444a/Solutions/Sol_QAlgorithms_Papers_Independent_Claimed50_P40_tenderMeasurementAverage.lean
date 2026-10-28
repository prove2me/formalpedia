-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P40.tenderMeasurementAverage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:54:40.7147+00:00
-- url     : https://prove2.me/submissions/9ca6fe08-36a5-4b73-a9aa-9f0867f707bc

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

namespace T40P40

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma sqrt_psd (Y : Matrix n n ℂ) : (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma sqrt_mul_sqrt {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

noncomputable def fq (P : Matrix n n ℂ) : ℝ := (Pᴴ * P).trace.re

lemma fq_nonneg (P : Matrix n n ℂ) : 0 ≤ fq P := by
  have := (Matrix.posSemidef_conjTranspose_mul_self P).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma re_tr_swap (P Q : Matrix n n ℂ) : (Qᴴ * P).trace.re = (Pᴴ * Q).trace.re := by
  have : (Qᴴ * P).trace = star ((Pᴴ * Q).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [this]; simp

lemma cs (P Q : Matrix n n ℂ) : (Pᴴ * Q).trace.re ≤ Real.sqrt (fq P) * Real.sqrt (fq Q) := by
  have hq : ∀ t : ℝ, 0 ≤ fq Q * (t * t) + (-2 * (Pᴴ * Q).trace.re) * t + fq P := by
    intro t
    have h := fq_nonneg (P - (t : ℂ) • Q)
    unfold fq at h ⊢
    have e : (P - (t : ℂ) • Q)ᴴ * (P - (t : ℂ) • Q) =
        Pᴴ * P - (t : ℂ) • (Pᴴ * Q) - (t : ℂ) • (Qᴴ * P) + ((t : ℂ) * t) • (Qᴴ * Q) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
      module
    rw [e] at h
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re, Complex.add_re,
      smul_eq_mul, Complex.re_ofReal_mul, ← Complex.ofReal_mul] at h
    rw [re_tr_swap P Q] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h2 : ((Pᴴ * Q).trace.re) ^ 2 ≤ fq P * fq Q := by nlinarith
  calc (Pᴴ * Q).trace.re ≤ |(Pᴴ * Q).trace.re| := le_abs_self _
    _ = Real.sqrt (((Pᴴ * Q).trace.re) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (fq P * fq Q) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (fq P) * Real.sqrt (fq Q) := Real.sqrt_mul (fq_nonneg P) _

lemma fq_contr {Z : Matrix n n ℂ} (hZ : Z.IsHermitian) (h : (1 - Z * Z).PosSemidef)
    (C : Matrix n n ℂ) : fq (Z * C) ≤ fq C := by
  have hp := h.conjTranspose_mul_mul_same C
  have := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  unfold fq
  rw [Matrix.conjTranspose_mul, hZ.eq]
  have e : Cᴴ * (1 - Z * Z) * C = Cᴴ * C - Cᴴ * Z * (Z * C) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, Matrix.trace_sub, Complex.sub_re] at this
  simp only [Matrix.mul_assoc] at this ⊢
  linarith

lemma core (X Y Z : Matrix n n ℂ) (hZ : Z.IsHermitian) (h : (1 - Z * Z).PosSemidef) :
    (Z * (X * Xᴴ - Y * Yᴴ)).trace.re ≤ Real.sqrt (fq (X + Y)) * Real.sqrt (fq (X - Y)) := by
  set u := X + Y; set v := X - Y
  have e : X * Xᴴ - Y * Yᴴ = (1 / 2 : ℂ) • (v * uᴴ + u * vᴴ) := by
    simp only [u, v, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add]
  have t1 : (Z * (v * uᴴ)).trace = (uᴴ * (Z * v)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have t2 : (Z * (u * vᴴ)).trace = (vᴴ * (Z * u)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [t1, t2]
  have c1 := cs u (Z * v)
  have c2 := cs v (Z * u)
  have k1 := Real.sqrt_le_sqrt (fq_contr hZ h v)
  have k2 := Real.sqrt_le_sqrt (fq_contr hZ h u)
  have s1 := Real.sqrt_nonneg (fq u)
  have s2 := Real.sqrt_nonneg (fq v)
  rw [smul_eq_mul]
  have : ((1 / 2 : ℂ) * ((uᴴ * (Z * v)).trace + (vᴴ * (Z * u)).trace)).re =
      (1 / 2) * ((uᴴ * (Z * v)).trace.re + (vᴴ * (Z * u)).trace.re) := by
    simp [Complex.mul_re]
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left k1 s1, mul_le_mul_of_nonneg_left k2 s2]

lemma fq_tr {X : Matrix n n ℂ} : fq X = (X * Xᴴ).trace.re := by
  unfold fq; rw [Matrix.trace_mul_comm]

lemma fq_add (X Y : Matrix n n ℂ) : fq (X + Y) = fq X + fq Y + 2 * (Xᴴ * Y).trace.re := by
  unfold fq
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re, Complex.add_re, re_tr_swap Y X]
  ring

lemma fq_sub (X Y : Matrix n n ℂ) : fq (X - Y) = fq X + fq Y - 2 * (Xᴴ * Y).trace.re := by
  have := fq_add X (-Y)
  rw [← sub_eq_add_neg] at this
  rw [this]
  unfold fq
  simp [Matrix.trace_neg]
  ring

lemma sum_psd {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma one_sub_sq {Z : Matrix n n ℂ} (hZ : Z.IsHermitian) (h1 : (1 - Z).PosSemidef)
    (h2 : (1 + Z).PosSemidef) : (1 - Z * Z).PosSemidef := by
  have hsa : IsSelfAdjoint Z := hZ
  have hle : ∀ t ∈ spectrum ℝ Z, t ≤ 1 := by
    have : Z ≤ algebraMap ℝ (Matrix n n ℂ) 1 := by
      rw [map_one, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]; exact h1
    exact (le_algebraMap_iff_spectrum_le).mp this
  have hge : ∀ t ∈ spectrum ℝ Z, -1 ≤ t := by
    have : algebraMap ℝ (Matrix n n ℂ) (-1) ≤ Z := by
      rw [map_neg, map_one, ← sub_nonneg, sub_neg_eq_add, add_comm, Matrix.nonneg_iff_posSemidef]
      exact h2
    exact (algebraMap_le_iff_le_spectrum).mp this
  have e : 1 - Z * Z = cfc (fun t : ℝ => 1 - t * t) Z := by
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun t : ℝ => t * t) Z, cfc_const_one ℝ Z,
      cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Z, cfc_id' ℝ Z]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  nlinarith [hle t ht, hge t ht]

lemma tr_psd_mul {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, sqrt_mul_sqrt hQ, Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma x_cfc_psd (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma x_traceNorm_herm {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

/-- sign matrix of a Hermitian matrix. -/
lemma sgn_trace {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ Z : Matrix n n ℂ, Z.IsHermitian ∧ (1 - Z).PosSemidef ∧ (1 + Z).PosSemidef ∧
      (Z * H).trace.re = QAlgorithms.traceNorm H := by
  have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hfin := H.finite_real_spectrum
  set g : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1 with hg
  refine ⟨cfc g H, (cfc_predicate g H).isHermitian, ?_, ?_, ?_⟩
  · rw [← cfc_one ℝ H, ← cfc_sub (1 : ℝ → ℝ) g H (hfin.continuousOn _) (hfin.continuousOn _)]
    apply x_cfc_psd
    intro t; simp only [hg, Pi.one_apply]; split_ifs <;> norm_num
  · rw [← cfc_one ℝ H, ← cfc_add H (1 : ℝ → ℝ) g (hfin.continuousOn _) (hfin.continuousOn _)]
    apply x_cfc_psd
    intro t; simp only [hg, Pi.one_apply]; split_ifs <;> norm_num
  · rw [x_traceNorm_herm hH, ← Complex.add_re, ← Matrix.trace_add,
      ← cfc_add H (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
    have : cfc g H * H = cfc (fun t => g t * t) H := by
      rw [cfc_mul g (fun t : ℝ => t) H (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ H]
    rw [this]
    congr 3
    funext t
    simp only [hg]
    rcases le_total 0 t with h | h
    · simp [h]
    · rcases eq_or_lt_of_le h with h' | h'
      · simp [h']
      · simp [not_le.mpr h', h'.le]

/-- √D - D ≥ 0 for 0 ≤ D ≤ 1. -/
lemma sqrt_sub_psd {Dm : Matrix n n ℂ} (hD : Dm.PosSemidef) (hD1 : (1 - Dm).PosSemidef) :
    (cfc Real.sqrt Dm - Dm).PosSemidef := by
  have hsa : IsSelfAdjoint Dm := hD.1.isSelfAdjoint
  have hnn : (0 : Matrix n n ℂ) ≤ Dm := Matrix.nonneg_iff_posSemidef.mpr hD
  have hle : ∀ t ∈ spectrum ℝ Dm, t ≤ 1 := by
    have : Dm ≤ algebraMap ℝ (Matrix n n ℂ) 1 := by
      rw [map_one, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]; exact hD1
    exact (le_algebraMap_iff_spectrum_le).mp this
  have e : cfc Real.sqrt Dm - Dm = cfc (fun t : ℝ => Real.sqrt t - t) Dm := by
    rw [cfc_sub Real.sqrt (fun t : ℝ => t) Dm, cfc_id' ℝ Dm]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  have h0 := spectrum_nonneg_of_nonneg hnn ht
  have h1 := hle t ht
  have hs := Real.sqrt_nonneg t
  have hss := Real.mul_self_sqrt h0
  nlinarith

/-- gentle measurement, single branch. -/
lemma gentle {ρ Dm Z : Matrix n n ℂ} (hρ : ρ.PosSemidef) (tρ : ρ.trace = 1)
    (hDm : Dm.PosSemidef) (hD1 : (1 - Dm).PosSemidef) (hZ : Z.IsHermitian)
    (hZZ : (1 - Z * Z).PosSemidef) :
    (Z * (ρ - cfc Real.sqrt Dm * ρ * cfc Real.sqrt Dm)).trace.re ≤
      Real.sqrt (4 * (1 - (Dm * ρ).trace.re)) := by
  set S := cfc Real.sqrt Dm with hS
  set R := cfc Real.sqrt ρ with hR
  have hSH : Sᴴ = S := (sqrt_psd Dm).1.eq
  have hRH : Rᴴ = R := (sqrt_psd ρ).1.eq
  have hSS : S * S = Dm := sqrt_mul_sqrt hDm
  have hRR : R * R = ρ := sqrt_mul_sqrt hρ
  have hXX : R * Rᴴ = ρ := by rw [hRH, hRR]
  have hYY : (S * R) * (S * R)ᴴ = S * ρ * S := by
    rw [Matrix.conjTranspose_mul, hRH, hSH, ← hRR]; simp only [Matrix.mul_assoc]
  have hc := core R (S * R) Z hZ hZZ
  rw [hXX, hYY] at hc
  have fX : fq R = 1 := by rw [fq_tr, hXX, tρ]; simp
  have fY : fq (S * R) = (Dm * ρ).trace.re := by
    rw [fq_tr, hYY, Matrix.trace_mul_cycle, hSS]
  have h1D : 0 ≤ ((1 - Dm) * ρ).trace.re := tr_psd_mul hD1 hρ
  have e1D : ((1 - Dm) * ρ).trace.re = 1 - (Dm * ρ).trace.re := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, tρ]; simp
  have hdiff : 0 ≤ ((cfc Real.sqrt Dm - Dm) * ρ).trace.re := tr_psd_mul (sqrt_sub_psd hDm hD1) hρ
  have fXY : fq (R - S * R) ≤ 1 - (Dm * ρ).trace.re := by
    have e : R - S * R = (1 - S) * R := by rw [Matrix.sub_mul, Matrix.one_mul]
    rw [e, fq_tr]
    have e2 : (1 - S) * R * ((1 - S) * R)ᴴ = (1 - S) * ρ * (1 - S) := by
      rw [Matrix.conjTranspose_mul, hRH, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hSH,
        ← hRR]
      simp only [Matrix.mul_assoc]
    rw [e2, Matrix.trace_mul_cycle]
    have e3 : (1 - S) * (1 - S) = (1 - Dm) - (2 : ℂ) • (S - Dm) := by
      rw [← hSS]; ext i j
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e3, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul]
    have h2 : ∀ w : ℂ, ((2 : ℂ) * w).re = 2 * w.re := fun w => by simp [Complex.mul_re]
    rw [h2]
    rw [← hS] at hdiff
    linarith
  have hsum : fq (R + S * R) + fq (R - S * R) = 2 * fq R + 2 * fq (S * R) := by
    rw [fq_add, fq_sub]; ring
  have ha := fq_nonneg (R + S * R)
  have hcn := fq_nonneg (R - S * R)
  refine hc.trans ?_
  rw [← Real.sqrt_mul ha]
  apply Real.sqrt_le_sqrt
  have hY1 : (Dm * ρ).trace.re ≤ 1 := by linarith
  nlinarith

/-- a PSD branch contributes at most its trace. -/
lemma branch {Z P : Matrix n n ℂ} (hZ : (1 + Z).PosSemidef) (hP : P.PosSemidef) :
    (Z * (-P)).trace.re ≤ P.trace.re := by
  have h := tr_psd_mul hZ hP
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at h
  rw [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]
  linarith

end T40P40

namespace T40P40

lemma branch_psd {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef)
    (Dm : Matrix (Fin d) (Fin d) ℂ) :
    (cfc Real.sqrt Dm * ρ * cfc Real.sqrt Dm).PosSemidef := by
  have h := hρ.mul_mul_conjTranspose_same (cfc Real.sqrt Dm)
  rwa [(sqrt_psd Dm).1.eq] at h

lemma branch_tr {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) {Dm : Matrix (Fin d) (Fin d) ℂ}
    (hD : Dm.PosSemidef) :
    (cfc Real.sqrt Dm * ρ * cfc Real.sqrt Dm).trace = (Dm * ρ).trace := by
  rw [Matrix.trace_mul_cycle, sqrt_mul_sqrt hD]

lemma combine {B : Type*} [Fintype B] [DecidableEq B] {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ)
    (hD : IsPOVM D) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ) (φ : B)
    (ε : ℝ) (hε : 0 < ε) (herr : 1 - effectProb (D φ) ρ ≤ ε)
    (Zs : B → Matrix (Fin d) (Fin d) ℂ) (hH : ∀ b, (Zs b).IsHermitian)
    (h1 : ∀ b, (1 - Zs b).PosSemidef) (h2 : ∀ b, (1 + Zs b).PosSemidef) :
    (Zs φ * (ρ - ludersBranch D ρ φ)).trace.re +
      ∑ b ∈ Finset.univ.erase φ, (Zs b * (-ludersBranch D ρ b)).trace.re ≤
      Real.sqrt (8 * ε) + ε := by
  have hsum : 1 - D φ = ∑ b ∈ Finset.univ.erase φ, D b := by
    rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ φ)]; abel
  have hD1 : (1 - D φ).PosSemidef := by rw [hsum]; exact sum_psd _ _ hD.1
  have hg := gentle hρ.1 hρ.2 (hD.1 φ) hD1 (hH φ) (one_sub_sq (hH φ) (h1 φ) (h2 φ))
  have hb : ∀ b ∈ Finset.univ.erase φ, (Zs b * (-ludersBranch D ρ b)).trace.re ≤
      (D b * ρ).trace.re := by
    intro b _
    have := branch (h2 b) (branch_psd hρ.1 (D b))
    rwa [branch_tr ρ (hD.1 b)] at this
  have hs := Finset.sum_le_sum hb
  have htot : ∑ b ∈ Finset.univ.erase φ, (D b * ρ).trace.re = 1 - (D φ * ρ).trace.re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, ← hsum, Matrix.sub_mul,
      Matrix.one_mul, Matrix.trace_sub, hρ.2]
    simp
  unfold effectProb at herr
  have he : 0 ≤ 1 - (D φ * ρ).trace.re := by
    have := tr_psd_mul hD1 hρ.1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hρ.2] at this; simpa using this
  have hq : Real.sqrt (4 * (1 - (D φ * ρ).trace.re)) ≤ Real.sqrt (8 * ε) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold ludersBranch at hs ⊢
  linarith

lemma combine2 {B : Type*} [Fintype B] [DecidableEq B] {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ)
    (hD : IsPOVM D) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ) (φ : B)
    (Zs : B → Matrix (Fin d) (Fin d) ℂ) (hH : ∀ b, (Zs b).IsHermitian)
    (h1 : ∀ b, (1 - Zs b).PosSemidef) (h2 : ∀ b, (1 + Zs b).PosSemidef) :
    (Zs φ * (ρ - ludersBranch D ρ φ)).trace.re +
      ∑ b ∈ Finset.univ.erase φ, (Zs b * (-ludersBranch D ρ b)).trace.re ≤
      Real.sqrt (4 * (1 - effectProb (D φ) ρ)) + (1 - effectProb (D φ) ρ) := by
  have hsum : 1 - D φ = ∑ b ∈ Finset.univ.erase φ, D b := by
    rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ φ)]; abel
  have hD1 : (1 - D φ).PosSemidef := by rw [hsum]; exact sum_psd _ _ hD.1
  have hg := gentle hρ.1 hρ.2 (hD.1 φ) hD1 (hH φ) (one_sub_sq (hH φ) (h1 φ) (h2 φ))
  have hb : ∀ b ∈ Finset.univ.erase φ, (Zs b * (-ludersBranch D ρ b)).trace.re ≤
      (D b * ρ).trace.re := by
    intro b _
    have := branch (h2 b) (branch_psd hρ.1 (D b))
    rwa [branch_tr ρ (hD.1 b)] at this
  have hs := Finset.sum_le_sum hb
  have htot : ∑ b ∈ Finset.univ.erase φ, (D b * ρ).trace.re = 1 - (D φ * ρ).trace.re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, ← hsum, Matrix.sub_mul,
      Matrix.one_mul, Matrix.trace_sub, hρ.2]
    simp
  unfold effectProb
  have he : 0 ≤ 1 - (D φ * ρ).trace.re := by
    have := tr_psd_mul hD1 hρ.1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hρ.2] at this; simpa using this
  unfold ludersBranch at hs ⊢
  linarith

lemma block_trace {B : Type*} [Fintype B] [DecidableEq B] {d : ℕ} (Z : Matrix (B × Fin d) (B × Fin d) ℂ)
    (K : B → Matrix (Fin d) (Fin d) ℂ) :
    (Z * Matrix.of (fun y x : B × Fin d => if y.1 = x.1 then K y.1 y.2 x.2 else 0)).trace =
      ∑ b, (Z.submatrix (fun i => (b, i)) (fun i => (b, i)) * K b).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · simp


lemma ps1 {B : Type*} [Fintype B] [DecidableEq B] {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ)
    (hD : IsPOVM D) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ) (φ : B) :
    traceNorm (ρ - tenderOperation D ρ) ≤
      Real.sqrt (4 * (1 - effectProb (D φ) ρ)) + (1 - effectProb (D φ) ρ) := by
  have hT : (tenderOperation D ρ).PosSemidef := sum_psd _ _ (fun b => branch_psd hρ.1 (D b))
  obtain ⟨Z, hZ, hZ1, hZ2, hZt⟩ := sgn_trace (hρ.1.1.sub hT.1)
  rw [← hZt]
  have e : ρ - tenderOperation D ρ = (ρ - ludersBranch D ρ (φ)) +
      ∑ b ∈ Finset.univ.erase (φ), (-ludersBranch D ρ b) := by
    unfold tenderOperation
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (φ)), Finset.sum_neg_distrib]; abel
  rw [e, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_sum, Matrix.trace_sum,
    Complex.re_sum]
  exact combine2 D hD ρ hρ (φ) (fun _ => Z) (fun _ => hZ)
    (fun _ => hZ1) (fun _ => hZ2)

lemma ps2 {B : Type*} [Fintype B] [DecidableEq B] {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ)
    (hD : IsPOVM D) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ) (φ : B) :
    traceNorm (idealLabel φ ρ - labelledOperation D ρ) ≤
      Real.sqrt (4 * (1 - effectProb (D φ) ρ)) + (1 - effectProb (D φ) ρ) := by
  set K : B → Matrix (Fin d) (Fin d) ℂ :=
    fun b => (if b = φ then ρ else 0) - ludersBranch D ρ b with hK
  have hKH : ∀ b, (K b).IsHermitian := by
    intro b
    have h0 : (if b = φ then ρ else 0 : Matrix (Fin d) (Fin d) ℂ).IsHermitian := by
      split_ifs
      · exact hρ.1.1
      · exact Matrix.isHermitian_zero
    exact h0.sub (branch_psd hρ.1 (D b)).1
  have e : idealLabel (φ) ρ - labelledOperation D ρ =
      Matrix.of (fun y x : B × Fin d => if y.1 = x.1 then K y.1 y.2 x.2 else 0) := by
    ext ⟨b, i⟩ ⟨c, j⟩
    simp only [idealLabel, labelledOperation, Matrix.sub_apply, Matrix.of_apply, hK]
    by_cases hbc : b = c
    · subst hbc
      by_cases hb : b = φ <;> simp [hb]
    · have hn : ¬(b = φ ∧ c = φ) := fun h => hbc (h.1.trans h.2.symm)
      simp [hbc, hn]
  have hHH : (Matrix.of (fun y x : B × Fin d => if y.1 = x.1 then K y.1 y.2 x.2 else 0)).IsHermitian := by
    ext ⟨b, i⟩ ⟨c, j⟩
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases hbc : b = c
    · subst hbc; simp only [if_true]; exact (hKH b).apply i j
    · simp [hbc, Ne.symm hbc]
  rw [e]
  obtain ⟨Z, hZ, hZ1, hZ2, hZt⟩ := sgn_trace hHH
  rw [← hZt, block_trace, Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (φ))]
  set f : B → Fin d → B × Fin d := fun b i => (b, i)
  have hinj : ∀ b, Function.Injective (f b) := fun b i j h => (Prod.ext_iff.mp h).2
  have hK1 : K (φ) = ρ - ludersBranch D ρ (φ) := by simp [hK]
  have hK2 : ∀ b ∈ Finset.univ.erase (φ), K b = -ludersBranch D ρ b := by
    intro b hb
    simp [hK, Finset.ne_of_mem_erase hb]
  rw [hK1, Finset.sum_congr rfl (fun b hb => by rw [hK2 b hb])]
  refine combine2 D hD ρ hρ (φ)
    (fun b => Z.submatrix (f b) (f b)) (fun b => hZ.submatrix (f b)) ?_ ?_
  · intro b
    have := hZ1.submatrix (f b)
    have eq : (1 - Z).submatrix (f b) (f b) = 1 - Z.submatrix (f b) (f b) := by
      ext i j; simp [Matrix.one_apply, f]
    rwa [eq] at this
  · intro b
    have := hZ2.submatrix (f b)
    have eq : (1 + Z).submatrix (f b) (f b) = 1 + Z.submatrix (f b) (f b) := by
      ext i j; simp [Matrix.one_apply, f]
    rwa [eq] at this


lemma delta_bd {B : Type*} [Fintype B] [DecidableEq B] {d : ℕ} (D : B → Matrix (Fin d) (Fin d) ℂ)
    (hD : IsPOVM D) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ) (φ : B) :
    0 ≤ 1 - effectProb (D φ) ρ ∧ 1 - effectProb (D φ) ρ ≤ 1 := by
  have hsum : 1 - D φ = ∑ b ∈ Finset.univ.erase φ, D b := by
    rw [← hD.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ φ)]; abel
  have hD1 : (1 - D φ).PosSemidef := by rw [hsum]; exact sum_psd _ _ hD.1
  have h0 := tr_psd_mul (hD.1 φ) hρ.1
  have he := tr_psd_mul hD1 hρ.1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hρ.2] at he
  unfold effectProb
  constructor
  · simpa using he
  · linarith

lemma avg {A : Type*} (p δ t : A → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp : Summable p)
    (hp1 : ∑' a, p a = 1) (hδ0 : ∀ a, 0 ≤ δ a) (hδ1 : ∀ a, δ a ≤ 1)
    (ht : ∀ a, t a ≤ Real.sqrt (4 * δ a) + δ a) (e : ℝ) (he : 0 ≤ e)
    (hS : ∑' a, p a * δ a ≤ e) :
    ∑' a, p a * t a ≤ Real.sqrt (8 * e) + e := by
  have hRHS : 0 ≤ Real.sqrt (8 * e) + e := by positivity
  by_cases hs : Summable (fun a => p a * t a)
  swap
  · rw [tsum_eq_zero_of_not_summable hs]; exact hRHS
  have hδs : Summable (fun a => p a * δ a) :=
    Summable.of_nonneg_of_le (fun a => mul_nonneg (hp0 a) (hδ0 a))
      (fun a => mul_le_of_le_one_right (hp0 a) (hδ1 a)) hp
  have hrs : Summable (fun a => p a * Real.sqrt (δ a)) :=
    Summable.of_nonneg_of_le (fun a => mul_nonneg (hp0 a) (Real.sqrt_nonneg _))
      (fun a => mul_le_of_le_one_right (hp0 a) (Real.sqrt_le_one.mpr (hδ1 a))) hp
  set S := ∑' a, p a * δ a with hSdef
  set X := ∑' a, p a * Real.sqrt (δ a) with hXdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun a => mul_nonneg (hp0 a) (hδ0 a))
  have hX0 : 0 ≤ X := tsum_nonneg (fun a => mul_nonneg (hp0 a) (Real.sqrt_nonneg _))
  have hT : ∀ τ : ℝ, 0 < τ → X ≤ S / (2 * τ) + τ / 2 := by
    intro τ hτ
    have hsum2 : Summable (fun a => p a * δ a / (2 * τ) + p a * (τ / 2)) :=
      (hδs.div_const _).add (hp.mul_right _)
    have hle : X ≤ ∑' a, (p a * δ a / (2 * τ) + p a * (τ / 2)) := by
      refine Summable.tsum_le_tsum (fun a => ?_) hrs hsum2
      have hq := Real.sq_sqrt (hδ0 a)
      have hsq : 2 * τ * Real.sqrt (δ a) ≤ δ a + τ ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt (δ a) - τ)]
      have : Real.sqrt (δ a) ≤ δ a / (2 * τ) + τ / 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]; nlinarith
      calc p a * Real.sqrt (δ a) ≤ p a * (δ a / (2 * τ) + τ / 2) :=
            mul_le_mul_of_nonneg_left this (hp0 a)
        _ = _ := by ring
    rw [Summable.tsum_add (hδs.div_const _) (hp.mul_right _), tsum_div_const, tsum_mul_right,
      hp1, one_mul] at hle
    exact hle
  have key : X ≤ Real.sqrt S := by
    rcases eq_or_lt_of_le hS0 with h0 | hpos
    · rw [← h0, Real.sqrt_zero]
      by_contra hc
      have := hT X (not_le.mp hc)
      rw [← h0, zero_div] at this
      linarith [not_le.mp hc]
    · have hsq := Real.sqrt_pos.mpr hpos
      have := hT (Real.sqrt S) hsq
      have hh := Real.sq_sqrt hS0
      have : S / (2 * Real.sqrt S) + Real.sqrt S / 2 = Real.sqrt S := by
        field_simp; nlinarith
      linarith
  have h4 : ∀ x : ℝ, Real.sqrt (4 * x) = 2 * Real.sqrt x := by
    intro x
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsum3 : Summable (fun a => 2 * (p a * Real.sqrt (δ a)) + p a * δ a) :=
    (hrs.mul_left 2).add hδs
  have hle : ∑' a, p a * t a ≤ ∑' a, (2 * (p a * Real.sqrt (δ a)) + p a * δ a) := by
    refine Summable.tsum_le_tsum (fun a => ?_) hs hsum3
    have := mul_le_mul_of_nonneg_left (ht a) (hp0 a)
    rw [h4] at this
    linarith
  rw [Summable.tsum_add (hrs.mul_left 2) hδs, tsum_mul_left] at hle
  have hSe : Real.sqrt S ≤ Real.sqrt e := Real.sqrt_le_sqrt hS
  have h8 : 2 * Real.sqrt e ≤ Real.sqrt (8 * e) := by
    rw [← h4]; exact Real.sqrt_le_sqrt (by linarith)
  linarith

end T40P40

open T40P40 in
theorem solution {A B : Type*} [Fintype B] [DecidableEq B] {d : ℕ}
    (block : Fin d → ℕ) (rho : A → Matrix (Fin d) (Fin d) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a) ∧ InBlocks block (rho a))
    (D : B → Matrix (Fin d) (Fin d) ℂ) (hD : IsPOVM D)
    (hblock : ∀ b, InBlocks block (D b)) (phi : A → B) (P : PMF A)
    (epsilonBar : ℝ) (hepsilonBar : 0 ≤ epsilonBar)
    (herror : (∑' a, (P a).toReal * (1 - effectProb (D (phi a)) (rho a))) ≤ epsilonBar) :
    (∑' a, (P a).toReal * traceNorm (rho a - tenderOperation D (rho a))) ≤
      Real.sqrt (8 * epsilonBar) + epsilonBar ∧
    (∑' a, (P a).toReal *
      traceNorm (idealLabel (phi a) (rho a) - labelledOperation D (rho a))) ≤
      Real.sqrt (8 * epsilonBar) + epsilonBar := by
  have hp0 : ∀ a, 0 ≤ (P a).toReal := fun a => ENNReal.toReal_nonneg
  have hp : Summable (fun a => (P a).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have hp1 : ∑' a, (P a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top P a), PMF.tsum_coe]; rfl
  constructor
  · exact avg _ _ _ hp0 hp hp1 (fun a => (delta_bd D hD _ (hrho a).1 (phi a)).1)
      (fun a => (delta_bd D hD _ (hrho a).1 (phi a)).2)
      (fun a => ps1 D hD _ (hrho a).1 (phi a)) epsilonBar hepsilonBar herror
  · exact avg _ _ _ hp0 hp hp1 (fun a => (delta_bd D hD _ (hrho a).1 (phi a)).1)
      (fun a => (delta_bd D hD _ (hrho a).1 (phi a)).2)
      (fun a => ps2 D hD _ (hrho a).1 (phi a)) epsilonBar hepsilonBar herror
