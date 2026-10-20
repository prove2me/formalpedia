-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.choiChannelCorrespondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:18:17.190978+00:00
-- url     : https://prove2.me/submissions/7fc7026b-fb09-402e-84ce-634a33c91b07

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

lemma g52e_single_conj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (a b : Fin n) (o p : Fin m) :
    (A * Matrix.single a b (1 : ℂ) * Aᴴ) o p = A o a * star (A p b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.conjTranspose_apply]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Matrix.single_apply, hc, Ne.symm hc]
    · simp
  · intro c _ hc
    have : (A * Matrix.single a b (1 : ℂ)) o c = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [Matrix.single_apply, hc, Ne.symm hc]
    rw [this, zero_mul]
  · simp

lemma g52e_G1 {h k m : ℕ} (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (M : Matrix (Fin h) (Fin h) ℂ) :
    krausApply E M = fromOutputFirstChoi (krausChoi E) M := by
  ext o p
  simp only [krausApply, fromOutputFirstChoi, QAlgorithms.Papers.Independent.Information100.P34.fromChoi,
    krausChoi, Matrix.sum_apply, dyad, operatorKet, PiLp.toLp_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

lemma g52e_G2 {h k m : ℕ} (E : Fin m → Matrix (Fin k) (Fin h) ℂ) :
    outputFirstChoi (krausApply E) = krausChoi E := by
  ext ⟨o, i⟩ ⟨p, j⟩
  show krausApply E (Matrix.single i j 1) o p = _
  simp only [krausApply, krausChoi, Matrix.sum_apply, g52e_single_conj, dyad, operatorKet,
    PiLp.toLp_apply, RCLike.star_def]

lemma g52e_G3 {h k m : ℕ} (E : Fin m → Matrix (Fin k) (Fin h) ℂ) :
    traceLeft (krausChoi E) = (∑ l, (E l)ᴴ * E l)ᵀ := by
  ext i j
  simp only [traceLeft, krausChoi, Matrix.of_apply, Matrix.sum_apply, dyad, operatorKet,
    PiLp.toLp_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun o _ => ?_
  ring

lemma g52e_G5 {h k n : ℕ} (A : Fin n → Matrix (Fin k) (Fin h) ℂ) : (krausChoi A).PosSemidef := by
  unfold krausChoi
  refine Matrix.posSemidef_sum _ fun l _ => ?_
  have : dyad (operatorKet (A l)) (operatorKet (A l)) =
      Matrix.vecMulVec (⇑(operatorKet (A l))) (star ⇑(operatorKet (A l))) := by
    ext p q; simp [dyad, Matrix.vecMulVec_apply]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma g52e_G7 {h k : ℕ} (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) :
    outputFirstChoi (fromOutputFirstChoi X) = X := by
  ext ⟨o, i⟩ ⟨p, j⟩
  show fromOutputFirstChoi X (Matrix.single i j 1) o p = _
  simp only [fromOutputFirstChoi, QAlgorithms.Papers.Independent.Information100.P34.fromChoi]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
  · simp
  · intro b _ hb; refine Finset.sum_eq_zero fun c _ => ?_; simp [Matrix.single_apply, Ne.symm hb]
  · simp

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma g52e_G5' {h k : ℕ} (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) (hX : X.PosSemidef) :
    ∃ (n : ℕ) (A : Fin n → Matrix (Fin k) (Fin h) ℂ), X = krausChoi A := by
  classical
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  let e := Fintype.equivFin (Fin k × Fin h)
  refine ⟨Fintype.card (Fin k × Fin h), fun l o i => conj (B (e.symm l) (o, i)), ?_⟩
  ext p q
  simp only [krausChoi, Matrix.sum_apply, dyad, operatorKet, PiLp.toLp_apply, Complex.conj_conj,
    Matrix.mul_apply, Matrix.star_apply, RCLike.star_def]
  exact (Fintype.sum_equiv e.symm _ _ (fun l => rfl)).symm

lemma g52e_trK {h k m : ℕ} (E : Fin m → Matrix (Fin k) (Fin h) ℂ) (ρ : Matrix (Fin h) (Fin h) ℂ) :
    (krausApply E ρ).trace = (ρ * ∑ l, (E l)ᴴ * E l).trace := by
  unfold krausApply
  rw [Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]

lemma g52e_unitvec {h : ℕ} (S : Matrix (Fin h) (Fin h) ℂ)
    (hS : ∀ ρ : Matrix (Fin h) (Fin h) ℂ, IsDensityMatrix ρ → (ρ * S).trace = 1)
    (u : Fin h → ℂ) (hu : u ≠ 0) :
    (Matrix.vecMulVec u (star u) * S).trace = (Matrix.vecMulVec u (star u)).trace := by
  set t : ℝ := ∑ a, Complex.normSq (u a) with ht
  have htr : (Matrix.vecMulVec u (star u)).trace = (t : ℂ) := by
    simp [Matrix.trace, Matrix.vecMulVec_apply, ht, Complex.mul_conj]
  have hpos : 0 < t := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
    have : 0 < Complex.normSq (u a) := Complex.normSq_pos.mpr ha
    exact lt_of_lt_of_le this (Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (u b))
      (Finset.mem_univ a))
  have hd : IsDensityMatrix (((t⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec u (star u)) := by
    refine ⟨(Matrix.posSemidef_vecMulVec_self_star u).smul ?_, ?_⟩
    · exact_mod_cast (inv_nonneg.mpr hpos.le)
    · rw [Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne',
        Complex.ofReal_one]
  have := hS _ hd
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at this
  have hT : (t : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast at this
  rw [htr, show (Matrix.vecMulVec u (star u) * S).trace =
    (t : ℂ) * ((t : ℂ)⁻¹ * (Matrix.vecMulVec u (star u) * S).trace) by field_simp, this, mul_one]

lemma g52e_S1 {h : ℕ} (S : Matrix (Fin h) (Fin h) ℂ)
    (hS : ∀ ρ : Matrix (Fin h) (Fin h) ℂ, IsDensityMatrix ρ → (ρ * S).trace = 1) : S = 1 := by
  have key : ∀ u : Fin h → ℂ, u ≠ 0 →
      ∑ a, ∑ b, u a * star (u b) * S b a = ∑ a, u a * star (u a) := by
    intro u hu
    have := g52e_unitvec S hS u hu
    simpa [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply] using this
  ext i j
  by_cases hij : i = j
  · subst hij
    have := key (Pi.single i 1) (by simp)
    simpa [Pi.single_apply, Matrix.one_apply] using this
  · have h1 := key (Pi.single i 1 + Pi.single j 1) (fun h0 => by
      have := congrFun h0 i; simp [Pi.single_apply, hij] at this)
    have h2 := key (Pi.single i 1 + Pi.single j Complex.I) (fun h0 => by
      have := congrFun h0 i; simp [Pi.single_apply, hij] at this)
    have hi := key (Pi.single i 1) (by simp)
    have hj := key (Pi.single j 1) (by simp)
    have hji : j ≠ i := Ne.symm hij
    simp [Pi.single_apply, hij, hji, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ), Complex.conj_I]
      at h1 h2 hi hj
    rw [Matrix.one_apply_ne hij]
    linear_combination (1/2 : ℂ) * h1 - (Complex.I / 2) * h2
      + (-1/2 + Complex.I / 2) * hi + (-1/2 + Complex.I / 2) * hj
      + ((S i j - S j i) / 2) * Complex.I_sq

/-- PDF p.3, (13)–(15) and the one-to-one correspondence credited to [14]–[16].
Includes reconstruction on every matrix, positivity's Kraus converse, both channel
correspondence directions, and the all-density trace-one test. -/
theorem solution {h k m : ℕ} (hh : 0 < h) (hk : 0 < k)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) :
    (∀ M, krausApply E M = fromOutputFirstChoi (krausChoi E) M) ∧
    outputFirstChoi (krausApply E) = krausChoi E ∧
    (IsKrausFamily E ↔ traceLeft (krausChoi E) = 1) ∧
    ((∀ rho, IsDensityMatrix rho → (krausApply E rho).trace = 1) ↔
      traceLeft (krausChoi E) = 1) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ,
      X.PosSemidef ↔ ∃ (n : ℕ) (A : Fin n → Matrix (Fin k) (Fin h) ℂ), X = krausChoi A) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ,
      ChoiFeasible X ↔ IsChannel (fromOutputFirstChoi X)) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ, outputFirstChoi (fromOutputFirstChoi X) = X) ∧
    (∀ B : Superop (Fin h) (Fin k), IsChannel B → fromOutputFirstChoi (outputFirstChoi B) = B) := by
  have hKF : ∀ {n : ℕ} (A : Fin n → Matrix (Fin k) (Fin h) ℂ),
      IsKrausFamily A ↔ traceLeft (krausChoi A) = 1 := by
    intro n A
    rw [g52e_G3]
    unfold IsKrausFamily
    constructor
    · intro hA; rw [hA, Matrix.transpose_one]
    · intro hA
      have := congrArg Matrix.transpose hA
      simpa using this
  refine ⟨g52e_G1 E, g52e_G2 E, hKF E, ?_, ?_, ?_, g52e_G7, ?_⟩
  · rw [← hKF]
    unfold IsKrausFamily
    constructor
    · intro hT
      exact g52e_S1 _ fun ρ hρ => by rw [← g52e_trK]; exact hT ρ hρ
    · intro hA ρ hρ
      rw [g52e_trK, hA, Matrix.mul_one, hρ.2]
  · intro X
    exact ⟨g52e_G5' X, fun ⟨n, A, hA⟩ => hA ▸ g52e_G5 A⟩
  · intro X
    constructor
    · rintro ⟨hpsd, htl⟩
      obtain ⟨n, A, rfl⟩ := g52e_G5' X hpsd
      exact ⟨n, A, (hKF A).mpr htl, fun ρ => (g52e_G1 A ρ).symm⟩
    · rintro ⟨n, A, hA, hEq⟩
      have hX : X = krausChoi A := by
        rw [← g52e_G7 X, ← g52e_G2 A]
        congr 1
        funext ρ
        exact hEq ρ
      rw [hX]
      exact ⟨g52e_G5 A, (hKF A).mp hA⟩
  · rintro B ⟨n, A, -, hB⟩
    have hJ : outputFirstChoi B = krausChoi A := by
      rw [← g52e_G2 A]
      congr 1
      funext ρ
      exact hB ρ
    rw [hJ]
    funext M
    rw [← g52e_G1, hB]


end

