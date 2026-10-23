-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.j2_basis_coefficient_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:26:41.875458+00:00
-- url     : https://prove2.me/submissions/af4a0806-527b-4645-b074-a87dc1224bf5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50BC

open QAlgorithms.Papers.Independent.Dependency50.P50

lemma j2_apply {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (p q : Fin n × Fin m) : j2 T p q = T (Matrix.single p.1 q.1 1) p.2 q.2 := rfl

lemma expand2 {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin m) :
    T A a b = ∑ c : Fin n × Fin n, A c.1 c.2 * T (Matrix.single c.1 c.2 1) a b := by
  have hA : A = ∑ i : Fin n, ∑ j : Fin n, A i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp [Matrix.smul_single]
  conv_lhs => rw [hA]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type]

lemma kron_apply {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (a c : Fin n) (b d : Fin m) : Matrix.kronecker A B (a, b) (c, d) = A a c * B b d := rfl

lemma single_ne {n : ℕ} (b : Fin n × Fin n) (p1 q1 : Fin n) (hb : b ≠ (p1, q1)) :
    Matrix.single b.1 b.2 (1 : ℂ) p1 q1 = 0 := by
  rw [Matrix.single_apply]
  split_ifs with h
  · exact absurd (Prod.ext h.1 h.2) hb
  · rfl

lemma part1 {n m : ℕ} (F : (Fin n × Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    j2Family F T =
      ∑ b : Fin n × Fin n, ∑ c : Fin n × Fin n,
        (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) •
          Matrix.kronecker (Matrix.single b.1 b.2 1) (T (Matrix.single c.1 c.2 1)) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have hL : j2Family F T (p1, p2) (q1, q2) =
      ∑ a : Fin n × Fin n, F a p1 q1 * T (F a) p2 q2 := by
    simp only [j2Family, Matrix.sum_apply, kron_apply]
  have hR : (∑ b : Fin n × Fin n, ∑ c : Fin n × Fin n,
        (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) •
          Matrix.kronecker (Matrix.single b.1 b.2 (1 : ℂ)) (T (Matrix.single c.1 c.2 1)))
        (p1, p2) (q1, q2) =
      ∑ c : Fin n × Fin n, (∑ a : Fin n × Fin n, F a p1 q1 * F a c.1 c.2) *
        T (Matrix.single c.1 c.2 1) p2 q2 := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, kron_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (p1, q1)]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [single_ne b p1 q1 hb]; ring
    · simp
  rw [hL, hR]
  simp only [expand2 T (F _), Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  ring

lemma j2_eq_sum {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    j2 T = ∑ b : Fin n × Fin n,
      Matrix.kronecker (Matrix.single b.1 b.2 1) (T (Matrix.single b.1 b.2 1)) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rw [j2_apply]
  simp only [Matrix.sum_apply, kron_apply]
  rw [Finset.sum_eq_single (p1, q1)]
  · simp
  · intro b _ hb
    rw [single_ne b p1 q1 hb, zero_mul]
  · simp

lemma entry {n m : ℕ} (F : (Fin n × Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (p1 q1 : Fin n) (p2 q2 : Fin m) :
    j2Family F T (p1, p2) (q1, q2) =
      ∑ c : Fin n × Fin n, (∑ a : Fin n × Fin n, F a p1 q1 * F a c.1 c.2) *
        T (Matrix.single c.1 c.2 1) p2 q2 := by
  simp only [j2Family, Matrix.sum_apply, kron_apply]
  simp only [expand2 T (F _), Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- test map reading off one coordinate -/
def coordMap {n m : ℕ} (hm : 0 < m) (c : Fin n × Fin n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun A := A c.1 c.2 • Matrix.single ⟨0, hm⟩ ⟨0, hm⟩ 1
  map_add' A B := by simp [add_smul]
  map_smul' r A := by simp

lemma coordMap_single {n m : ℕ} (hm : 0 < m) (c d : Fin n × Fin n) :
    coordMap hm c (Matrix.single d.1 d.2 1) ⟨0, hm⟩ ⟨0, hm⟩ = if d = c then 1 else 0 := by
  simp only [coordMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply,
    Matrix.single_apply_same, smul_eq_mul, mul_one, Matrix.single_apply]
  by_cases h : d = c
  · subst h; simp
  · simp only [h, if_false]
    rw [if_neg]
    intro h'
    exact h (Prod.ext h'.1 h'.2)

lemma part2 {n m : ℕ} (hm : 0 < m) (F : (Fin n × Fin n) → Matrix (Fin n) (Fin n) ℂ) :
    (∀ T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ), j2Family F T = j2 T) ↔
      ∀ b c : Fin n × Fin n,
        (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) = if b = c then 1 else 0 := by
  constructor
  · intro h b c
    have h2 := congrFun (congrFun (h (coordMap hm c)) (b.1, ⟨0, hm⟩)) (b.2, ⟨0, hm⟩)
    rw [entry, j2_apply] at h2
    simp only [coordMap_single, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h2
    exact h2
  · intro h T
    rw [part1, j2_eq_sum]
    simp only [h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma phase_eq : phaseBasis = ⇑((Matrix.stdBasis ℂ (Fin 2) (Fin 2)).unitsSMul
    (fun _ => Units.mk0 Complex.I Complex.I_ne_zero)) := by
  funext a
  rw [Module.Basis.unitsSMul_apply, Matrix.stdBasis_eq_single]
  rfl

end X6P50BC

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50BC in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (F : Module.Basis (Fin n × Fin n) ℂ ((Matrix (Fin n) (Fin n) ℂ))) :
    ((∀ T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ),
        j2Family F T =
          ∑ b : Fin n × Fin n, ∑ c : Fin n × Fin n,
            (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) •
              Matrix.kronecker (Matrix.single b.1 b.2 1) (T (Matrix.single c.1 c.2 1))) ∧
      ((∀ T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ), j2Family F T = j2 T) ↔
        ∀ b c : Fin n × Fin n,
          (∑ a : Fin n × Fin n, F a b.1 b.2 * F a c.1 c.2) =
            if b = c then 1 else 0)) ∧
      (LinearIndependent ℂ phaseBasis ∧
        Submodule.span ℂ (Set.range phaseBasis) = ⊤ ∧
        j2Family phaseBasis (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)) ≠
          j2 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) := by
  refine ⟨⟨fun T => part1 F T, part2 hm F⟩, ?_, ?_, ?_⟩
  · rw [phase_eq]; exact Module.Basis.linearIndependent _
  · rw [phase_eq]; exact Module.Basis.span_eq _
  · intro h
    have := congrFun (congrFun h (0, 0)) (0, 0)
    rw [j2_apply] at this
    simp [j2Family, phaseBasis, Fintype.sum_prod_type, Fin.sum_univ_two] at this
    norm_num at this
