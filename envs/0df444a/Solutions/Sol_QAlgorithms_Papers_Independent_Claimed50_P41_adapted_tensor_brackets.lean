-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.adapted_tensor_brackets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:30:09.077833+00:00
-- url     : https://prove2.me/submissions/34117989-1870-4c13-8753-900f6d3064ba

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4Adapted

open QAlgorithms.Papers.Independent.Claimed50.P41

variable {R : Type*} [Ring R] [Algebra ℂ R]

lemma cm_add_left (A B C : R) : algebraCommutator (A + B) C = algebraCommutator A C + algebraCommutator B C := by
  simp only [algebraCommutator, add_mul, mul_add]; abel
lemma cm_sub_left (A B C : R) : algebraCommutator (A - B) C = algebraCommutator A C - algebraCommutator B C := by
  simp only [algebraCommutator, sub_mul, mul_sub]; abel
lemma cm_add_right (A B C : R) : algebraCommutator C (A + B) = algebraCommutator C A + algebraCommutator C B := by
  simp only [algebraCommutator, add_mul, mul_add]; abel
lemma cm_sub_right (A B C : R) : algebraCommutator C (A - B) = algebraCommutator C A - algebraCommutator C B := by
  simp only [algebraCommutator, sub_mul, mul_sub]; abel
lemma cm_smul_left (c : ℂ) (A C : R) : algebraCommutator (c • A) C = c • algebraCommutator A C := by
  simp only [algebraCommutator, smul_mul_assoc, mul_smul_comm, smul_sub]
lemma cm_smul_right (c : ℂ) (A C : R) : algebraCommutator C (c • A) = c • algebraCommutator C A := by
  simp only [algebraCommutator, smul_mul_assoc, mul_smul_comm, smul_sub]

variable {n : ℕ}

@[simp] lemma sig_ll (i j : Fin n) : sigma n (Sum.inl i) (Sum.inl j) = 0 := by simp [sigma]
@[simp] lemma sig_lr (i j : Fin n) : sigma n (Sum.inl i) (Sum.inr j) = if i = j then 1 else 0 := by
  simp [sigma, Matrix.one_apply]
@[simp] lemma sig_rl (i j : Fin n) : sigma n (Sum.inr i) (Sum.inl j) = -(if i = j then 1 else 0) := by
  simp [sigma, Matrix.one_apply]
@[simp] lemma sig_rr (i j : Fin n) : sigma n (Sum.inr i) (Sum.inr j) = 0 := by simp [sigma]

lemma Xrl (rho : GeneratorRepresentation n R) (i j : Fin n) :
    rho.X (Sum.inr i) (Sum.inl j) = rho.X (Sum.inl j) (Sum.inr i) := rho.symmetric _ _

lemma t1 (rho : GeneratorRepresentation n R) (r s u v : Fin n) :
    algebraCommutator (adaptedA rho r s) (adaptedA rho u v) =
        kronecker s u • adaptedA rho r v - kronecker r v • adaptedA rho u s := by
  simp only [adaptedA, compactQ, compactJ, splitV, splitW, splitZ, tensorLower, tensorUpper,
    cm_add_left, cm_sub_left,
    cm_add_right, cm_sub_right, cm_smul_left, cm_smul_right, rho.bracket, sig_ll, sig_lr, sig_rl, sig_rr,
    kronecker]
  simp only [Xrl rho]
  split_ifs <;> subst_vars <;> (try simp only [rho.symmetric]) <;> (try push_cast) <;> match_scalars <;> ring_nf <;> norm_num [Complex.ext_iff, pow_succ]

lemma t2 (rho : GeneratorRepresentation n R) (r s u v : Fin n) :
    algebraCommutator (adaptedA rho r s) (tensorLower rho u v) =
        kronecker s u • tensorLower rho r v + kronecker s v • tensorLower rho r u := by
  simp only [adaptedA, compactQ, compactJ, splitV, splitW, splitZ, tensorLower, tensorUpper,
    cm_add_left, cm_sub_left,
    cm_add_right, cm_sub_right, cm_smul_left, cm_smul_right, rho.bracket, sig_ll, sig_lr, sig_rl, sig_rr,
    kronecker]
  simp only [Xrl rho]
  split_ifs <;> subst_vars <;> (try simp only [rho.symmetric]) <;> (try push_cast) <;> match_scalars <;> ring_nf <;> norm_num [Complex.ext_iff, pow_succ]

lemma t3 (rho : GeneratorRepresentation n R) (r s u v : Fin n) :
    algebraCommutator (adaptedA rho r s) (tensorUpper rho u v) =
        -kronecker r u • tensorUpper rho s v - kronecker r v • tensorUpper rho s u := by
  simp only [adaptedA, compactQ, compactJ, splitV, splitW, splitZ, tensorLower, tensorUpper,
    cm_add_left, cm_sub_left,
    cm_add_right, cm_sub_right, cm_smul_left, cm_smul_right, rho.bracket, sig_ll, sig_lr, sig_rl, sig_rr,
    kronecker]
  simp only [Xrl rho]
  split_ifs <;> subst_vars <;> (try simp only [rho.symmetric]) <;> (try push_cast) <;> match_scalars <;> ring_nf <;> norm_num [Complex.ext_iff, pow_succ]

lemma t4 (rho : GeneratorRepresentation n R) (r s u v : Fin n) :
    algebraCommutator (tensorLower rho r s) (tensorUpper rho u v) =
        (-4 : ℂ) • (kronecker r u • adaptedA rho s v + kronecker r v • adaptedA rho s u +
          kronecker s u • adaptedA rho r v + kronecker s v • adaptedA rho r u) := by
  simp only [adaptedA, compactQ, compactJ, splitV, splitW, splitZ, tensorLower, tensorUpper,
    cm_add_left, cm_sub_left,
    cm_add_right, cm_sub_right, cm_smul_left, cm_smul_right, rho.bracket, sig_ll, sig_lr, sig_rl, sig_rr,
    kronecker]
  simp only [Xrl rho]
  split_ifs <;> subst_vars <;> (try simp only [rho.symmetric]) <;> (try push_cast) <;> match_scalars <;> ring_nf <;> norm_num [Complex.ext_iff, pow_succ]

lemma t5 (rho : GeneratorRepresentation n R) (r s u v : Fin n) :
    algebraCommutator (tensorLower rho r s) (tensorLower rho u v) = 0 := by
  simp only [adaptedA, compactQ, compactJ, splitV, splitW, splitZ, tensorLower, tensorUpper,
    cm_add_left, cm_sub_left,
    cm_add_right, cm_sub_right, cm_smul_left, cm_smul_right, rho.bracket, sig_ll, sig_lr, sig_rl, sig_rr,
    kronecker]
  simp only [Xrl rho]
  split_ifs <;> subst_vars <;> (try simp only [rho.symmetric]) <;> (try push_cast) <;> match_scalars <;> ring_nf <;> norm_num [Complex.ext_iff, pow_succ]

lemma t6 (rho : GeneratorRepresentation n R) (r s u v : Fin n) :
    algebraCommutator (tensorUpper rho r s) (tensorUpper rho u v) = 0 := by
  simp only [adaptedA, compactQ, compactJ, splitV, splitW, splitZ, tensorLower, tensorUpper,
    cm_add_left, cm_sub_left,
    cm_add_right, cm_sub_right, cm_smul_left, cm_smul_right, rho.bracket, sig_ll, sig_lr, sig_rl, sig_rr,
    kronecker]
  simp only [Xrl rho]
  split_ifs <;> subst_vars <;> (try simp only [rho.symmetric]) <;> (try push_cast) <;> match_scalars <;> ring_nf <;> norm_num [Complex.ext_iff, pow_succ]


lemma sym_parts (rho : GeneratorRepresentation n R) (r s : Fin n) :
    tensorLower rho r s = tensorLower rho s r ∧ tensorUpper rho r s = tensorUpper rho s r := by
  simp only [tensorLower, tensorUpper, splitV, splitW, splitZ]
  rw [rho.symmetric (Sum.inl r) (Sum.inl s), rho.symmetric (Sum.inr r) (Sum.inr s), add_comm (rho.X _ (Sum.inr s))]
  exact ⟨rfl, rfl⟩

variable [StarRing R] [StarModule ℂ R]

lemma star_A (rho : GeneratorRepresentation n R)
    (h : ∀ r s : Fin n, star (compactJ rho r s) = compactJ rho r s ∧
      star (compactQ rho r s) = compactQ rho r s) (r s : Fin n) :
    star (adaptedA rho r s) = adaptedA rho s r := by
  have hQ : compactQ rho s r = compactQ rho r s := by
    simp only [compactQ, splitV, splitZ]
    rw [rho.symmetric (Sum.inl s), rho.symmetric (Sum.inr s)]
  have hJ : compactJ rho s r = -compactJ rho r s := by
    simp only [compactJ]; abel
  simp only [adaptedA, star_smul, star_sub, (h r s).1, (h r s).2, hQ, hJ]
  simp [Complex.conj_I]

lemma star_T (rho : GeneratorRepresentation n R) (h : ∀ a b, star (rho.X a b) = rho.X a b)
    (r s : Fin n) : star (tensorLower rho r s) = tensorUpper rho r s := by
  simp only [tensorLower, tensorUpper, splitV, splitW, splitZ, star_sub, star_add, star_smul, h]
  simp [Complex.conj_I]
  module

end X4Adapted

open QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (_hn : 0 < n)
    (R : Type*) [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
    (rho : GeneratorRepresentation n R) :
    (∀ r s : Fin n, tensorLower rho r s = tensorLower rho s r ∧
      tensorUpper rho r s = tensorUpper rho s r) ∧
    (∀ r s u v : Fin n,
      algebraCommutator (adaptedA rho r s) (adaptedA rho u v) =
        kronecker s u • adaptedA rho r v - kronecker r v • adaptedA rho u s ∧
      algebraCommutator (adaptedA rho r s) (tensorLower rho u v) =
        kronecker s u • tensorLower rho r v + kronecker s v • tensorLower rho r u ∧
      algebraCommutator (adaptedA rho r s) (tensorUpper rho u v) =
        -kronecker r u • tensorUpper rho s v - kronecker r v • tensorUpper rho s u ∧
      algebraCommutator (tensorLower rho r s) (tensorUpper rho u v) =
        (-4 : ℂ) • (kronecker r u • adaptedA rho s v + kronecker r v • adaptedA rho s u +
          kronecker s u • adaptedA rho r v + kronecker s v • adaptedA rho r u) ∧
      algebraCommutator (tensorLower rho r s) (tensorLower rho u v) = 0 ∧
      algebraCommutator (tensorUpper rho r s) (tensorUpper rho u v) = 0) ∧
    ((∀ r s : Fin n, star (compactJ rho r s) = compactJ rho r s ∧
      star (compactQ rho r s) = compactQ rho r s) →
      ∀ r s : Fin n, star (adaptedA rho r s) = adaptedA rho s r) ∧
    ((∀ a b, star (rho.X a b) = rho.X a b) →
      ∀ r s : Fin n, star (tensorLower rho r s) = tensorUpper rho r s) :=
  ⟨X4Adapted.sym_parts rho, fun r s u v => ⟨X4Adapted.t1 rho r s u v, X4Adapted.t2 rho r s u v,
    X4Adapted.t3 rho r s u v, X4Adapted.t4 rho r s u v, X4Adapted.t5 rho r s u v, X4Adapted.t6 rho r s u v⟩,
    fun h => X4Adapted.star_A rho h, fun h => X4Adapted.star_T rho h⟩
