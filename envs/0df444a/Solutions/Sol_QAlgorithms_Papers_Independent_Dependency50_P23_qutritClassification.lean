-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P23.qutritClassification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:11:34.52806+00:00
-- url     : https://prove2.me/submissions/3a96fd15-1fc4-41c9-b52c-75773a9d96e0

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

lemma x8_ppt {I J : Type} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ)
    (hX : Entanglement.IsSeparablePositive X) (v : I → J → ℂ) :
    0 ≤ (∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * X (i, j') (i', j) * v i' j').re := by
  obtain ⟨q, w, A, B, hw, hd, rfl⟩ := hX
  have key : ∀ t, 0 ≤ (∑ i, ∑ j, ∑ i', ∑ j',
      conj (v i j) * (A t i i' * B t j' j) * v i' j').re := by
    intro t
    have hP : (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (A t) (B t)ᵀ).PosSemidef :=
      (hd t).1.1.kronecker (hd t).2.1.transpose
    have h := hP.dotProduct_mulVec_nonneg (fun p => v p.1 p.2)
    have h2 : star (fun p : I × J => v p.1 p.2) ⬝ᵥ
        (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (A t) (B t)ᵀ) *ᵥ (fun p => v p.1 p.2) =
        ∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * (A t i i' * B t j' j) * v i' j' := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum,
        Matrix.kroneckerMap_apply, Matrix.transpose_apply, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [h2] at h
    exact (Complex.nonneg_iff.1 h).1
  have hsum : (∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) *
      (∑ t, (w t : ℂ) • Matrix.kronecker (A t) (B t) : Matrix (I × J) (I × J) ℂ) (i, j') (i', j) * v i' j') =
      ∑ t, (w t : ℂ) * ∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * (A t i i' * B t j' j) * v i' j' := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun t _ => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (hw t) (key t)

def x8ρ0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 / 3 : ℂ) else 0

lemma x8ρ0_density : IsDensityMatrix x8ρ0 := by
  set c : ℂ := (((Real.sqrt 3)⁻¹ : ℝ) : ℂ)
  have hc : c * conj c = 1 / 3 := by
    simp only [c, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  let ψ : Fin 3 × Fin 3 → ℂ := fun p => if p.1 = p.2 then c else 0
  have h : x8ρ0 = Matrix.vecMulVec ψ (star ψ) := by
    ext p q
    simp only [x8ρ0, Matrix.of_apply, Matrix.vecMulVec_apply, ψ, Pi.star_apply, RCLike.star_def]
    by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2, hc]
  refine ⟨?_, ?_⟩
  · rw [h]; exact Matrix.posSemidef_vecMulVec_self_star ψ
  · simp [x8ρ0, Matrix.trace, Fintype.sum_prod_type]

lemma x8_notEB (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi / 4) :
    ¬ IsEB (qutrit alpha) := by
  intro h
  have hs : 0 < Real.sin alpha :=
    Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  let v : Fin 3 → Fin 3 → ℂ := ![![0, 0, 0], ![0, 1, 0], ![-1, 0, 0]]
  have H := x8_ppt _ (h 3 (by norm_num) x8ρ0 x8ρ0_density) v
  have hval : (∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) *
      idTensorSuperop (qutrit alpha) x8ρ0 (i, j') (i', j) * v i' j') =
      -(2 / 3 * (Real.sin alpha : ℂ)) := by
    simp [v, Fin.sum_univ_three, idTensorSuperop, qutrit, krausApply, qutritKraus, x8ρ0,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecHead,
      Matrix.vecTail, -Complex.ofReal_sin]
    ring
  rw [hval] at H
  simp [Complex.sin_ofReal_re] at H
  linarith

lemma x8_qs (alpha : ℝ) (y a x b : Fin 3) :
    qutrit alpha (Matrix.single y a 1) x b =
      qutritKraus alpha 0 x y * conj (qutritKraus alpha 0 b a) +
      qutritKraus alpha 1 x y * conj (qutritKraus alpha 1 b a) := by
  simp only [qutrit, krausApply, Fin.sum_univ_two, Matrix.add_apply, Matrix.mul_apply,
    Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

lemma x8_notHad (alpha : ℝ) : ¬ IsHadamard (qutrit alpha) := by
  rintro ⟨k, hk, U, hU, hTr, hEB⟩
  have hR : ∀ x y b a, ∑ j, U (x, j) y * conj (U (b, j) a) =
      qutrit alpha (Matrix.single y a 1) x b := by
    intro x y b a
    rw [← hTr]
    simp [traceRight, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
      ite_mul]
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → Fin k → ℂ, v = ![fun j => conj (U (1, j) 2), fun _ => 0,
      fun j => -conj (U (1, j) 0)] := ⟨_, rfl⟩
  have H := x8_ppt _ (hEB 3 (by norm_num) x8ρ0 x8ρ0_density) v
  set X := idTensorSuperop (fun rho : Matrix (Fin 3) (Fin 3) ℂ =>
    (traceLeft (U * rho * Uᴴ) : Matrix (Fin k) (Fin k) ℂ)) x8ρ0 with hXdef
  have hX : ∀ i j' i' j, X (i, j') (i', j) = (1 / 3 : ℂ) * ∑ b, U (b, j') i * conj (U (b, j) i') := by
    intro i j' i' j
    simp [hXdef, idTensorSuperop, traceLeft, Matrix.mul_apply, x8ρ0, Matrix.conjTranspose_apply,
      Finset.mul_sum, ite_and, ite_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hfac : (∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * X (i, j') (i', j) * v i' j') =
      (1 / 3 : ℂ) * ∑ i, ∑ i', ∑ b, (∑ j, conj (v i j) * conj (U (b, j) i')) *
        (∑ j', v i' j' * U (b, j') i) := by
    simp only [hX, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; arg 2; ext i'; arg 2; ext j; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; arg 2; ext i'; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; arg 2; ext i'; arg 2; ext b; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun j' _ => ?_
    ring
  have e0 : ∀ i' b, ∑ j, conj (v 0 j) * conj (U (b, j) i') =
      qutrit alpha (Matrix.single 2 i' 1) 1 b := by
    intro i' b; rw [← hR]; simp [hv]
  have e1 : ∀ i' b, ∑ j, conj (v 1 j) * conj (U (b, j) i') = 0 := by
    intro i' b; simp [hv]
  have e2 : ∀ i' b, ∑ j, conj (v 2 j) * conj (U (b, j) i') =
      -qutrit alpha (Matrix.single 0 i' 1) 1 b := by
    intro i' b; rw [← hR]; simp [hv, Finset.sum_neg_distrib]
  have g0 : ∀ i b, ∑ j, v 0 j * U (b, j) i = qutrit alpha (Matrix.single i 2 1) b 1 := by
    intro i b; rw [← hR]; simp [hv, mul_comm]
  have g1 : ∀ i b, ∑ j, v 1 j * U (b, j) i = 0 := by
    intro i b; simp [hv]
  have g2 : ∀ i b, ∑ j, v 2 j * U (b, j) i = -qutrit alpha (Matrix.single i 0 1) b 1 := by
    intro i b; rw [← hR]; simp [hv, mul_comm, Finset.sum_neg_distrib]
  rw [hfac] at H
  simp only [Fin.sum_univ_three, e0, e1, e2, g0, g1, g2] at H
  simp only [x8_qs] at H
  simp [qutritKraus] at H
  norm_num at H

theorem x8_main (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    ¬ IsEB (qutrit alpha) ∧ ¬ IsHadamard (qutrit alpha) :=
  ⟨x8_notEB alpha ha0 ha1, x8_notHad alpha⟩

end QAlgorithms.Papers.Independent.Dependency50.P23

end

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P23

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    ¬ IsEB (qutrit alpha) ∧ ¬ IsHadamard (qutrit alpha) := x8_main alpha ha0 ha1

end
