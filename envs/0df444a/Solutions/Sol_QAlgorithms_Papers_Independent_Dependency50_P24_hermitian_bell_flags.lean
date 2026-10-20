-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.hermitian_bell_flags
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:27:11.573651+00:00
-- url     : https://prove2.me/submissions/b38766cf-36e0-4fac-b44e-59f0df71dacf

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

lemma g52e_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : cfc Real.sqrt (X * X) = positivePart X + negativePart X := by
  have hsa : IsSelfAdjoint X := hX
  unfold positivePart negativePart
  rw [← cfc_add (R := ℝ) (a := X) (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  rw [← sq, ← cfc_pow_id (R := ℝ) X 2 hsa, ← cfc_comp (R := ℝ) Real.sqrt (fun x : ℝ => x ^ 2) X hsa]
  refine cfc_congr fun x _ => ?_
  simp only [Function.comp, Real.sqrt_sq_eq_abs]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

open scoped MatrixOrder in
lemma g52e_pos_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : (positivePart X).PosSemidef ∧ (negativePart X).PosSemidef := by
  have hsa : IsSelfAdjoint X := hX
  constructor
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg (fun x _ => le_max_right x 0)
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg (fun x _ => le_max_right (-x) 0)

lemma g52e_PN {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : positivePart X * negativePart X = 0 := by
  have hsa : IsSelfAdjoint X := hX
  unfold positivePart negativePart
  rw [← cfc_mul (R := ℝ) (a := X) (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  rw [cfc_congr (g := fun _ : ℝ => (0 : ℝ)), cfc_const_zero]
  intro x _
  rcases le_total 0 x with h | h
  · simp [max_eq_right (show -x ≤ 0 by linarith)]
  · simp [max_eq_right h]

lemma g52e_XPN {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : X = positivePart X - negativePart X := by
  have hsa : IsSelfAdjoint X := hX
  unfold positivePart negativePart
  rw [← cfc_sub (R := ℝ) (a := X) (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  conv_lhs => rw [← cfc_id' (R := ℝ) (a := X) (ha := hsa)]
  refine cfc_congr fun x _ => ?_
  rcases le_total 0 x with h | h
  · simp [max_eq_left h, max_eq_right (show -x ≤ 0 by linarith)]
  · simp [max_eq_right h, max_eq_left (show 0 ≤ -x by linarith)]

lemma g52e_kron_smul {α β : Type*} (A : Matrix α α ℂ) (c : ℂ) (B : Matrix β β ℂ) :
    Matrix.kronecker A (c • B) = c • Matrix.kronecker A B := by
  ext i j; simp [Matrix.kronecker]; ring

/-- PDF p.10, Eqs.(45)–(47): unnormalized spectral flags include p=0,1.
Only positive-mass branches are normalized. -/
theorem solution {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (X : Op (S × T)) (hherm : X.IsHermitian) (hnorm : traceNorm X = 1) :
    let P := positivePart X
    let N := negativePart X
    let p := P.trace.re
    P.PosSemidef ∧ N.PosSemidef ∧ P*N = 0 ∧ X = P-N ∧
    0 ≤ p ∧ p ≤ 1 ∧ N.trace.re = 1-p ∧
    xForm X = Matrix.kronecker (signedBell false false) P + Matrix.kronecker (signedBell false true) N ∧
    (0 < p → IsDensityMatrix ((p : ℂ)⁻¹ • P)) ∧
    (p < 1 → IsDensityMatrix (((1-p : ℝ) : ℂ)⁻¹ • N)) ∧
    (0 < p → p < 1 →
      (((p : ℂ)⁻¹ • P) * (((1-p : ℝ) : ℂ)⁻¹ • N)).trace = 0 ∧
      xForm X = (p : ℂ) • Matrix.kronecker (signedBell false false) ((p : ℂ)⁻¹ • P) +
        ((1-p : ℝ) : ℂ) • Matrix.kronecker (signedBell false true) (((1-p : ℝ) : ℂ)⁻¹ • N)) := by
  intro P N p
  have hXX : Xᴴ = X := hherm
  obtain ⟨hP, hN⟩ := g52e_pos_psd X hherm
  have hPN : P * N = 0 := g52e_PN X hherm
  have hXe : X = P - N := g52e_XPN X hherm
  have hsq : cfc Real.sqrt (X * X) = P + N := g52e_sqrt_sq X hherm
  have htn : (P + N).trace.re = 1 := by
    rw [← hsq, ← hnorm]; unfold traceNorm; rw [hXX]
  have hp0 : 0 ≤ p := by
    have := hP.trace_nonneg; rw [Complex.nonneg_iff] at this; exact this.1
  have hn0 : 0 ≤ N.trace.re := by
    have := hN.trace_nonneg; rw [Complex.nonneg_iff] at this; exact this.1
  have hNtr : N.trace.re = 1 - p := by
    rw [Matrix.trace_add, Complex.add_re] at htn; simp only [p]; linarith
  have hp1 : p ≤ 1 := by linarith
  have hPc : P.trace = (p : ℂ) := by
    have := hP.trace_nonneg; rw [Complex.nonneg_iff] at this
    exact Complex.ext (by simp [p]) (by simpa [P] using this.2.symm)
  have hNc : N.trace = ((1 - p : ℝ) : ℂ) := by
    have := hN.trace_nonneg; rw [Complex.nonneg_iff] at this
    exact Complex.ext (by simp [hNtr]) (by simpa [N] using this.2.symm)
  have hx : xForm X = Matrix.kronecker (signedBell false false) P +
      Matrix.kronecker (signedBell false true) N := by
    have hc : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hXXh : X * Xᴴ = X * X := by rw [hXX]
    have hXhX : Xᴴ * X = X * X := by rw [hXX]
    have hXent : ∀ a b, X a b = P a b - N a b := fun a b => by
      rw [hXe]; rfl
    ext ⟨⟨k1, k2⟩, s⟩ ⟨⟨l1, l2⟩, s'⟩
    simp only [xForm, hXXh, hXhX, hsq, hXX]
    fin_cases k1 <;> fin_cases k2 <;> fin_cases l1 <;> fin_cases l2 <;>
      simp [Matrix.kronecker, signedBell, pureDensity, hXent] <;>
      ring_nf <;> (try simp only [hc]) <;> ring_nf <;>
      (try (rw [← add_mul]; congr 1; have key := congrFun (congrFun hsq s) s'
            rw [Matrix.add_apply] at key; convert key using 3))
  refine ⟨hP, hN, hPN, hXe, hp0, hp1, hNtr, hx, ?_, ?_, ?_⟩
  · intro hp
    refine ⟨hP.smul ?_, ?_⟩
    · exact_mod_cast (inv_nonneg.mpr hp.le)
    · rw [Matrix.trace_smul, hPc, smul_eq_mul, inv_mul_cancel₀ (by exact_mod_cast hp.ne')]
  · intro hp
    have h1 : 0 < 1 - p := by linarith
    refine ⟨hN.smul ?_, ?_⟩
    · exact_mod_cast (inv_nonneg.mpr h1.le)
    · rw [Matrix.trace_smul, hNc, smul_eq_mul, inv_mul_cancel₀ (by exact_mod_cast h1.ne')]
  · intro hp0' hp1'
    have h1 : 0 < 1 - p := by linarith
    refine ⟨?_, ?_⟩
    · rw [Matrix.smul_mul, Matrix.mul_smul, hPN]; simp
    · have e1 : ((p : ℂ) * (p : ℂ)⁻¹) = 1 := mul_inv_cancel₀ (by exact_mod_cast hp0'.ne')
      have e2 : (((1 - p : ℝ) : ℂ) * ((1 - p : ℝ) : ℂ)⁻¹) = 1 :=
        mul_inv_cancel₀ (by exact_mod_cast h1.ne')
      rw [hx, g52e_kron_smul, g52e_kron_smul, smul_smul, smul_smul, e1, e2, one_smul, one_smul]


end

