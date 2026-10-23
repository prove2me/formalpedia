-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.j2_hilbertSchmidt_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:08:14.899588+00:00
-- url     : https://prove2.me/submissions/d295d34b-5378-48bd-aeba-19368bcd92e9

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50J2

open QAlgorithms.Papers.Independent.Dependency50.P50

lemma j2_apply {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (p q : Fin n × Fin m) : j2 T p q = T (Matrix.single p.1 q.1 1) p.2 q.2 := rfl

lemma j1_apply {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (p q : Fin n × Fin m) : j1 T p q = T (Matrix.single q.1 p.1 1) p.2 q.2 := rfl

/-- the map with prescribed J2 matrix -/
def invJ2 {n m : ℕ} (M : BipartiteMat n m) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun A := Matrix.of fun a b => ∑ i : Fin n, ∑ j : Fin n, A i j * M (i, a) (j, b)
  map_add' A B := by
    ext a b; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext a b; simp [Finset.mul_sum, mul_assoc]

lemma j2_invJ2 {n m : ℕ} (M : BipartiteMat n m) : j2 (invJ2 M) = M := by
  ext p q
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  rw [j2_apply]
  simp only [invJ2, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.single_apply,
    ite_and, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq]

lemma invJ2_j2 {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    invJ2 (j2 T) = T := by
  apply LinearMap.ext
  intro A
  ext a b
  have hA : A = ∑ i : Fin n, ∑ j : Fin n, A i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp [Matrix.smul_single]
  conv_rhs => rw [hA]
  simp only [invJ2, j2_apply, map_sum, map_smul, Matrix.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]

end X6P50J2

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50J2 in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    Function.Bijective (j2 (n := n) (m := m)) ∧
      ∀ T S : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ),
        hsPair (j2 T) (j2 S) = mapPair T S ∧
          hsPair (j1 T) (j1 S) = hsPair (j2 T) (j2 S) := by
  refine ⟨⟨fun T S h => ?_, fun M => ⟨invJ2 M, j2_invJ2 M⟩⟩, fun T S => ⟨?_, ?_⟩⟩
  · rw [← invJ2_j2 T, ← invJ2_j2 S, h]
  · simp only [hsPair, mapPair, j2_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · let e : (Fin n × Fin m) × (Fin n × Fin m) ≃ (Fin n × Fin m) × (Fin n × Fin m) :=
      { toFun := fun x => ((x.2.1, x.1.2), (x.1.1, x.2.2))
        invFun := fun x => ((x.2.1, x.1.2), (x.1.1, x.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simp only [hsPair]
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    rw [← e.sum_comp]
    rfl
