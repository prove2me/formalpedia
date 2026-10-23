-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P04.noAutomaticTensorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:53:33.032621+00:00
-- url     : https://prove2.me/submissions/053ca78f-bc96-4b39-8990-611237064073

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P04
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P04

lemma part1 (X Y : Matrix Bool Bool ℂ) :
    (Xᴴ * qubitK Y).trace = ((qubitK X)ᴴ * Y).trace := by
  simp [qubitK, Matrix.trace, Fintype.sum_bool, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  ring_nf

lemma hs_eq (X : Matrix Bool Bool ℂ) : hsQuadratic qubitK X =
    3/2 * (Complex.normSq (X false false) + Complex.normSq (X false true) +
      Complex.normSq (X true false) + Complex.normSq (X true true))
    - Complex.normSq (X false false + X true true) / 2 := by
  simp [hsQuadratic, qubitK, Matrix.trace, Fintype.sum_bool, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Complex.normSq_apply]
  ring


lemma herm_spec (Q : Matrix Bool Bool ℂ) (hQ : Q.IsHermitian) :
    let U : Matrix Bool Bool ℂ := (hQ.eigenvectorUnitary : Matrix Bool Bool ℂ)
    let D : Matrix Bool Bool ℂ := Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues)
    Q = U * D * star U ∧ star U * U = 1 ∧ U * star U = 1 ∧ D = star U * Q * U := by
  intro U D
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hQ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  · exact Unitary.coe_star_mul_self _
  · exact Unitary.coe_mul_star_self _
  · have := hQ.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this.symm

lemma hs_herm (Q : Matrix Bool Bool ℂ) (hQ : Q.IsHermitian) :
    hsQuadratic qubitK Q = hQ.eigenvalues false ^ 2 + hQ.eigenvalues true ^ 2
      - hQ.eigenvalues false * hQ.eigenvalues true := by
  obtain ⟨h1, h2, h3, h4⟩ := herm_spec Q hQ
  set U : Matrix Bool Bool ℂ := (hQ.eigenvectorUnitary : Matrix Bool Bool ℂ)
  set D : Matrix Bool Bool ℂ := Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues)
  have hQQ : (Q * Q).trace = (D * D).trace := by
    rw [h1]
    calc (U * D * star U * (U * D * star U)).trace = (U * (D * (star U * U) * D) * star U).trace := by
          simp only [Matrix.mul_assoc]
      _ = (D * D).trace := by
          rw [h2, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hT : Q.trace = D.trace := by
    rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have e : hsQuadratic qubitK Q = (3/2 * (Q * Q).trace - Q.trace * Q.trace / 2).re := by
    simp only [hsQuadratic, qubitK, hQ.eq]
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.mul_one, smul_eq_mul, smul_eq_mul]
    congr 1; ring
  rw [e, hQQ, hT]
  simp [D, Matrix.trace, Fintype.sum_bool, Matrix.diagonal_mul_diagonal]
  ring

open scoped Matrix.Norms.L2Operator in
lemma eig_le_norm (Q : Matrix Bool Bool ℂ) (hQ : Q.IsHermitian) (i : Bool) :
    |hQ.eigenvalues i| ≤ specNorm Q := by
  obtain ⟨h1, h2, h3, h4⟩ := herm_spec Q hQ
  set U : Matrix Bool Bool ℂ := (hQ.eigenvectorUnitary : Matrix Bool Bool ℂ)
  set D : Matrix Bool Bool ℂ := Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues)
  have hD : ‖D‖ ≤ ‖Q‖ := by
    rw [h4]
    calc ‖star U * Q * U‖ ≤ ‖star U * Q‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖star U‖ * ‖Q‖ * ‖U‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖Q‖ * 1 := by
          gcongr
          · exact le_of_eq (CStarRing.norm_coe_unitary (star hQ.eigenvectorUnitary))
          · exact le_of_eq (CStarRing.norm_coe_unitary hQ.eigenvectorUnitary)
      _ = ‖Q‖ := by ring
  have : |hQ.eigenvalues i| ≤ ‖D‖ := by
    rw [Matrix.l2_opNorm_diagonal]
    have := norm_le_pi_norm (RCLike.ofReal ∘ hQ.eigenvalues : Bool → ℂ) i
    simpa using this
  exact this.trans hD


lemma sum_f2 {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Bool) → M) :
    ∑ x, f x = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [piFinTwoEquiv]
  abel

lemma f2_cases (P : (Fin 2 → Bool) → Prop) (h00 : P ![false, false]) (h01 : P ![false, true])
    (h10 : P ![true, false]) (h11 : P ![true, true]) (x) : P x := by
  have : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [this]
  cases x 0 <;> cases x 1 <;> assumption

lemma B_mul : bellTwo * bellTwo = bellTwo := by
  ext i j
  simp only [Matrix.mul_apply, sum_f2]
  induction i using f2_cases <;> induction j using f2_cases <;> simp [bellTwo] <;> norm_num

lemma B_herm : bellTwoᴴ = bellTwo := by
  ext i j
  induction i using f2_cases <;> induction j using f2_cases <;> simp [bellTwo]

lemma qK_single (a b c d : Bool) : qubitK (Matrix.single a b 1) c d =
    (if c = a ∧ d = b then 3/2 else 0) - (if a = b ∧ c = d then 1/2 else 0) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [qubitK, Matrix.trace, Matrix.single_apply] <;> norm_num

lemma hs_B : hsQuadratic (piSuperop (fun _ : Fin 2 => qubitK)) bellTwo = 7/4 := by
  rw [hsQuadratic, B_herm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_f2, piSuperop, Matrix.of_apply,
    Fin.prod_univ_two, qK_single]
  simp [bellTwo]
  norm_num


lemma part2 (X : Matrix Bool Bool ℂ) (hX : X ≠ 0) : 0 < hsQuadratic qubitK X := by
  rw [hs_eq]
  have hne : ∃ i j, X i j ≠ 0 := by
    by_contra h; push Not at h; exact hX (Matrix.ext h)
  have key : Complex.normSq (X false false + X true true) ≤
      2 * Complex.normSq (X false false) + 2 * Complex.normSq (X true true) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((X false false).re - (X true true).re),
      sq_nonneg ((X false false).im - (X true true).im)]
  obtain ⟨i, j, hij⟩ := hne
  have hp := Complex.normSq_pos.mpr hij
  have n1 := Complex.normSq_nonneg (X false false)
  have n2 := Complex.normSq_nonneg (X false true)
  have n3 := Complex.normSq_nonneg (X true false)
  have n4 := Complex.normSq_nonneg (X true true)
  cases i <;> cases j <;> nlinarith

lemma part5 (Q : Matrix Bool Bool ℂ) (hQ : IsEffect Q) :
    hsQuadratic qubitK Q ≤ (specNorm Q) ^ 2 := by
  have hH : Q.IsHermitian := hQ.1.isHermitian
  rw [hs_herm Q hH]
  have a0 := hQ.1.eigenvalues_nonneg false
  have a1 := hQ.1.eigenvalues_nonneg true
  have b0 := eig_le_norm Q hH false
  have b1 := eig_le_norm Q hH true
  rw [abs_of_nonneg a0] at b0
  rw [abs_of_nonneg a1] at b1
  rcases le_total (hH.eigenvalues false) (hH.eigenvalues true) with h | h
  · nlinarith [mul_le_mul b1 b1 a1 (a1.trans b1)]
  · nlinarith [mul_le_mul b0 b0 a0 (a0.trans b0)]

lemma B_eff : IsEffect bellTwo := by
  constructor
  · have : bellTwo = bellTwoᴴ * bellTwo := by rw [B_herm, B_mul]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  · have : (1 - bellTwo) = (1 - bellTwo)ᴴ * (1 - bellTwo) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, B_herm, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, B_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

open scoped Matrix.Norms.L2Operator in
lemma B_norm : specNorm bellTwo = 1 := by
  show ‖bellTwo‖ = 1
  have h := Matrix.l2_opNorm_conjTranspose_mul_self bellTwo
  rw [B_herm, B_mul] at h
  have hne : bellTwo ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 ![false, false]) ![false, false]
    simp [bellTwo] at this
  have hpos : 0 < ‖bellTwo‖ := norm_pos_iff.mpr hne
  have : ‖bellTwo‖ * (‖bellTwo‖ - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · linarith

end X4P04

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P04 X4P04

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    (∀ X Y : Matrix Bool Bool ℂ, (Xᴴ * qubitK Y).trace = ((qubitK X)ᴴ * Y).trace) ∧
    (∀ X : Matrix Bool Bool ℂ, X ≠ 0 → 0 < hsQuadratic qubitK X) ∧
    qubitK 1 = (1/2:ℂ) • (1:Matrix Bool Bool ℂ) ∧
    (∀ X : Matrix Bool Bool ℂ, X.trace = 0 → qubitK X = (3/2:ℂ) • X) ∧
    (∀ Q : Matrix Bool Bool ℂ, IsEffect Q → hsQuadratic qubitK Q ≤ (specNorm Q)^2) ∧
    IsEffect bellTwo ∧ specNorm bellTwo = 1 ∧
    hsQuadratic (piSuperop (fun _ : Fin 2 => qubitK)) bellTwo = 7/4 ∧
    (specNorm bellTwo)^2 < hsQuadratic (piSuperop (fun _ : Fin 2 => qubitK)) bellTwo := by
  refine ⟨part1, part2, ?_, ?_, part5, B_eff, B_norm, hs_B, ?_⟩
  · ext i j; cases i <;> cases j <;> simp [qubitK, Matrix.trace] <;> norm_num
  · intro X hX; simp [qubitK, hX]
  · rw [B_norm, hs_B]; norm_num

end
