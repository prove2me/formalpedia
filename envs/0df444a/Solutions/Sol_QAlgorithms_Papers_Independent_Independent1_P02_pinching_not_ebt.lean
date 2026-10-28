-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.pinching_not_ebt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:43:22.493993+00:00
-- url     : https://prove2.me/submissions/364a5b6c-e272-49e2-9c80-ae163b7c70eb

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

theorem p02s204_peres {I J : Type*} [Fintype I] [Fintype J]
    (X : Matrix (I × J) (I × J) ℂ) (h : Entanglement.IsSeparablePositive X) :
    (Entanglement.partialTransposeFirst X).PosSemidef := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := h
  have : Entanglement.partialTransposeFirst (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
      ∑ j, (w j : ℂ) • Matrix.kronecker (A j)ᵀ (B j) := by
    ext p r
    simp [Entanglement.partialTransposeFirst, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ =>
    ((hAB j).1.1.transpose.kronecker (hAB j).2.1).smul (Complex.zero_le_real.mpr (hw j))

theorem p02s204_two {d : ℕ} (P : Algebra d) (h : 1 < P.rank) :
    ∃ u v : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℂ u v = 0 ∧
      (∃ x, u.ofLp = P *ᵥ x) ∧ (∃ y, v.ofLp = P *ᵥ y) := by
  set K := LinearMap.range (Matrix.toEuclideanLin P) with hK
  have hr : Module.finrank ℂ K = P.rank := by
    rw [Matrix.rank_eq_finrank_range_toLin P (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℂ).toBasis, ← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  let b := stdOrthonormalBasis ℂ K
  have h0 : 0 < Module.finrank ℂ K := by omega
  have h1 : 1 < Module.finrank ℂ K := by omega
  let i0 : Fin (Module.finrank ℂ K) := ⟨0, h0⟩
  let i1 : Fin (Module.finrank ℂ K) := ⟨1, h1⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨(b i0 : EuclideanSpace ℂ (Fin d)), (b i1 : EuclideanSpace ℂ (Fin d)), ?_, ?_, ?_, ?_, ?_⟩
  · exact b.orthonormal.1 i0
  · exact b.orthonormal.1 i1
  · have := b.orthonormal.2 hne
    simpa [Submodule.coe_inner] using this
  · obtain ⟨x, hx⟩ := (b i0).2
    exact ⟨x.ofLp, by rw [← hx]; rfl⟩
  · obtain ⟨x, hx⟩ := (b i1).2
    exact ⟨x.ofLp, by rw [← hx]; rfl⟩

theorem p02s204_fix {d m : ℕ} (E : Fin m → Algebra d) (k : Fin m)
    (hOrthogonal : ∀ j k, j ≠ k → E j * E k = 0) (hProjection : ∀ k, E k * E k = E k)
    (x y : Fin d → ℂ) (hx : ∃ x0, x = E k *ᵥ x0) (hy : ∃ y0, y = E k *ᵥ y0) :
    krausApply E (Matrix.vecMulVec x (star y)) = Matrix.vecMulVec x (star y) := by
  have act : ∀ (z : Fin d → ℂ), (∃ z0, z = E k *ᵥ z0) → ∀ j, E j *ᵥ z = if j = k then z else 0 := by
    rintro z ⟨z0, rfl⟩ j
    rw [Matrix.mulVec_mulVec]
    split_ifs with hj
    · subst hj; rw [hProjection]
    · rw [hOrthogonal j k hj, Matrix.zero_mulVec]
  unfold krausApply
  have term : ∀ j, E j * Matrix.vecMulVec x (star y) * (E j)ᴴ =
      Matrix.vecMulVec (E j *ᵥ x) (star (E j *ᵥ y)) := by
    intro j
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  simp only [term, act x hx, act y hy]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem p02s204_quad {d : ℕ} (f g : Fin 2 → Fin d → ℂ) :
    star (fun p : Fin 2 × Fin d => g p.1 p.2) ⬝ᵥ
      (Entanglement.partialTransposeFirst (Matrix.of fun p q : Fin 2 × Fin d =>
        (1/2 : ℂ) * (f p.1 p.2 * conj (f q.1 q.2))) *ᵥ (fun p => g p.1 p.2)) =
      (1/2 : ℂ) * ∑ a, ∑ b, (∑ i, conj (g a i) * f b i) * (∑ j, conj (f a j) * g b j) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Entanglement.partialTransposeFirst,
    Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

theorem p02s204_main (d m : ℕ) (E : Fin m → Algebra d)
    (hProjection : ∀ k, E k * E k = E k)
    (hOrthogonal : ∀ j k, j ≠ k → E j * E k = 0)
    (hLarge : ∃ k, 1 < (E k).rank) :
    ¬ Entanglement.IsEntanglementBreakingPositive (krausEndomorphism E) := by
  intro hEB
  obtain ⟨k, hk⟩ := hLarge
  obtain ⟨u, v, hu, hv, huv, hux, hvy⟩ := p02s204_two (E k) hk
  have inner_eq : ∀ a b : EuclideanSpace ℂ (Fin d), inner ℂ a b = ∑ i, conj (a i) * b i := by
    intro a b
    simp [PiLp.inner_apply, mul_comm]
  have huu : ∑ i, conj (u i) * u i = 1 := by
    rw [← inner_eq, inner_self_eq_norm_sq_to_K, hu]; simp
  have hvv : ∑ i, conj (v i) * v i = 1 := by
    rw [← inner_eq, inner_self_eq_norm_sq_to_K, hv]; simp
  have huv' : ∑ i, conj (u i) * v i = 0 := by rw [← inner_eq, huv]
  have hvu' : ∑ i, conj (v i) * u i = 0 := by
    rw [← inner_eq, ← inner_conj_symm, huv]; simp
  let f : Fin 2 → Fin d → ℂ := ![u.ofLp, v.ofLp]
  let X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
    Matrix.of fun p q => (1/2 : ℂ) * (f p.1 p.2 * conj (f q.1 q.2))
  have hXv : X = (1/2 : ℂ) • Matrix.vecMulVec (fun p => f p.1 p.2) (star fun p => f p.1 p.2) := by
    ext p q; simp [X, Matrix.vecMulVec_apply]
  have hXd : IsDensityMatrix X := by
    refine ⟨?_, ?_⟩
    · rw [hXv]
      exact (Matrix.posSemidef_vecMulVec_self_star _).smul
        (by simp)
    · simp only [X, Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
      have e1 : ∑ i, u i * conj (u i) = 1 := by rw [← huu]; simp [mul_comm]
      have e2 : ∑ i, v i * conj (v i) = 1 := by rw [← hvv]; simp [mul_comm]
      rw [e1, e2]; norm_num
  have hY : idTensorSuperop (krausEndomorphism E) X = X := by
    ext p q
    have blk : (Matrix.of fun i i' => X (p.1, i) (q.1, i')) =
        (1/2 : ℂ) • Matrix.vecMulVec (f p.1) (star (f q.1)) := by
      ext i i'; simp [X, Matrix.vecMulVec_apply]
    have hf : ∀ a, ∃ x0, f a = E k *ᵥ x0 := by
      intro a; fin_cases a
      · exact hux
      · exact hvy
    simp only [idTensorSuperop, Matrix.of_apply]
    rw [blk, map_smul]
    change ((1/2 : ℂ) • krausApply E (Matrix.vecMulVec (f p.1) (star (f q.1)))) p.2 q.2 = _
    rw [p02s204_fix E k hOrthogonal hProjection _ _ (hf p.1) (hf q.1)]
    simp [X, Matrix.vecMulVec_apply]
  have hsep := hEB 2 (by norm_num) X hXd
  rw [hY] at hsep
  have hpsd := p02s204_peres X hsep
  let g : Fin 2 → Fin d → ℂ := ![v.ofLp, -u.ofLp]
  have hz := hpsd.re_dotProduct_nonneg (fun p => g p.1 p.2)
  rw [p02s204_quad f g] at hz
  simp only [Fin.sum_univ_two, f, g, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.neg_apply,
    map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib] at hz
  rw [huu, hvv, huv', hvu'] at hz
  norm_num at hz

end QAlgorithms.Papers.Independent.Independent1.P02

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02 in
/-- Section 3, PDF p.9: a block pinching with a rank>1 block is not EBT. -/
theorem solution (d m : ℕ) (hd : 0 < d) (E : Fin m → Algebra d)
    (hHermitian : ∀ k, (E k).IsHermitian) (hProjection : ∀ k, E k * E k = E k)
    (hOrthogonal : ∀ j k, j ≠ k → E j * E k = 0) (hComplete : ∑ k, E k = 1)
    (hLarge : ∃ k, 1 < (E k).rank) :
    krausEndomorphism E ∉ ebtSet d := by
  intro h
  exact p02s204_main d m E hProjection hOrthogonal hLarge h.1

#print axioms solution
