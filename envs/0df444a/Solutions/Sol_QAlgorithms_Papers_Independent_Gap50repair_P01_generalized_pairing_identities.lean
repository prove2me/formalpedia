-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_pairing_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:49:51.427781+00:00
-- url     : https://prove2.me/submissions/06ca9df4-0917-4b96-9a95-5f11510f1c17

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZG

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma oc_sub_l (x x' y : Coord n → ℂ) : omegaC (x - x') y = omegaC x y - omegaC x' y := by
  unfold omegaC; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

lemma oc_sub_r (x y y' : Coord n → ℂ) : omegaC x (y - y') = omegaC x y - omegaC x y' := by
  unfold omegaC; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

lemma oc_smul_l (c : ℂ) (x y : Coord n → ℂ) : omegaC (c • x) y = c * omegaC x y := by
  unfold omegaC; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

lemma oc_smul_r (c : ℂ) (x y : Coord n → ℂ) : omegaC x (c • y) = c * omegaC x y := by
  unfold omegaC; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

lemma oc_zero_l (y : Coord n → ℂ) : omegaC 0 y = 0 := by simp [omegaC]

lemma oc_eq (x y : Coord n → ℂ) :
    omegaC x y = x ⬝ᵥ ((omegaMatrix n).map Complex.ofRealHom *ᵥ y) := by
  unfold omegaC omegaMatrix
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply,
    Finset.sum_sub_distrib, apply_ite, ite_mul, Finset.sum_ite_eq]
  ring

lemma J_eq (n : ℕ) : canonicalJ n = -omegaMatrix n := by
  unfold canonicalJ omegaMatrix
  rw [Matrix.fromBlocks_neg]; simp

lemma cx_eq (A : GroupedRealMatrix n) : complexify A = A.map Complex.ofRealHom := rfl

lemma oc_inv (A : GroupedRealMatrix n) (hA : IsSymplectic A) (x y : Coord n → ℂ) :
    omegaC (complexify A *ᵥ x) (complexify A *ᵥ y) = omegaC x y := by
  have h : Aᵀ * omegaMatrix n * A = omegaMatrix n := by
    unfold IsSymplectic at hA
    rw [J_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hA; exact hA
  rw [oc_eq, oc_eq, Matrix.mulVec_mulVec, cx_eq, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec,
    ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, h]

lemma sh_apply (A : GroupedRealMatrix n) (z : ℂ) (x : Coord n → ℂ) :
    shifted A z x = complexify A *ᵥ x - z • x := by
  simp [shifted, Matrix.toLin'_apply]

lemma pow_succ_apply (f : Module.End ℂ (Coord n → ℂ)) (i : ℕ) (x : Coord n → ℂ) :
    (f ^ (i+1)) x = f ((f ^ i) x) := by
  rw [pow_succ', Module.End.mul_apply]

lemma step (A : GroupedRealMatrix n) (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0)
    (x y : Coord n → ℂ) :
    omegaC x (shifted A z⁻¹ y) = -(1/z) * omegaC (shifted A z x) (shifted A z⁻¹ y) -
      (1/z^2) * omegaC (shifted A z x) y := by
  simp only [sh_apply, oc_sub_l, oc_sub_r, oc_smul_l, oc_smul_r, oc_inv A hA]
  field_simp
  ring

lemma vanish (A : GroupedRealMatrix n) (z : ℂ) (p : ℕ) (hn : HasNilpotentHeight A z p)
    (v : Coord n → ℂ) (hv : v ∈ generalizedSpace A z) (m : ℕ) (hm : p + 1 ≤ m) :
    (shifted A z ^ m) v = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, Module.End.mul_apply, hn.2 v hv, map_zero]

theorem main (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0) :
    (∀ v w : Coord n → ℂ, ∀ i j : ℕ, 0 < j →
      omegaC ((shifted A z^i) v) ((shifted A z⁻¹^j) w) =
      -(1/z)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^j) w) -
      (1/z^2)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^(j-1)) w)) ∧
    (IsEigenvalue A z → ∀ p, HasNilpotentHeight A z p →
      ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A z,
      (∀ k j : ℕ, j ≤ p+k → omegaC ((shifted A z^(p+k)) v) w =
        (-z^2)^j*omegaC ((shifted A z^(p+k-j)) v) ((shifted A z⁻¹^j) w)) ∧
      omegaC ((shifted A z^p) v) w = (-z^2)^p*omegaC v ((shifted A z⁻¹^p) w) ∧
      (∀ k j : ℕ, p < k+j → omegaC ((shifted A z^k) v) ((shifted A z⁻¹^j) w) = 0)) := by
  have part1 : ∀ v w : Coord n → ℂ, ∀ i j : ℕ, 0 < j →
      omegaC ((shifted A z^i) v) ((shifted A z⁻¹^j) w) =
      -(1/z)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^j) w) -
      (1/z^2)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^(j-1)) w) := by
    intro v w i j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ_apply (shifted A z⁻¹) j w, pow_succ_apply (shifted A z) i v]
    exact step A hA z hz0 _ _
  refine ⟨part1, ?_⟩
  intro _ p hn v hv w _
  have partc : ∀ k j : ℕ, p < k+j → omegaC ((shifted A z^k) v) ((shifted A z⁻¹^j) w) = 0 := by
    intro k j
    induction j generalizing k with
    | zero =>
      intro hk
      rw [vanish A z p hn v hv k (by omega), oc_zero_l]
    | succ j ih =>
      have : ∀ m k, p + 1 - k = m → p < k + (j+1) →
          omegaC ((shifted A z^k) v) ((shifted A z⁻¹^(j+1)) w) = 0 := by
        intro m
        induction m with
        | zero =>
          intro k hm _
          rw [vanish A z p hn v hv k (by omega), oc_zero_l]
        | succ m ihm =>
          intro k hm hk
          rw [part1 v w k (j+1) (by omega), ihm (k+1) (by omega) (by omega),
            Nat.add_sub_cancel, ih (k+1) (by omega)]
          ring
      exact this _ k rfl
  have parta : ∀ k j : ℕ, j ≤ p+k → omegaC ((shifted A z^(p+k)) v) w =
      (-z^2)^j*omegaC ((shifted A z^(p+k-j)) v) ((shifted A z⁻¹^j) w) := by
    intro k j hj
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [add_zero] at hj ⊢
      induction j with
      | zero => simp
      | succ j ih =>
        rw [ih (by omega)]
        have e := part1 v w (p - (j+1)) (j+1) (by omega)
        rw [show p - (j+1) + 1 = p - j by omega, partc (p - j) (j+1) (by omega),
          Nat.add_sub_cancel] at e
        rw [e]
        field_simp
        ring
    · rw [vanish A z p hn v hv (p+k) (by omega), oc_zero_l, partc (p+k-j) j (by omega), mul_zero]
  refine ⟨parta, ?_, partc⟩
  have := parta 0 p (by omega)
  simpa using this

end X4CZG

theorem solution {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0) :
    (∀ v w : Coord n → ℂ, ∀ i j : ℕ, 0 < j →
      omegaC ((shifted A z^i) v) ((shifted A z⁻¹^j) w) =
      -(1/z)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^j) w) -
      (1/z^2)*omegaC ((shifted A z^(i+1)) v) ((shifted A z⁻¹^(j-1)) w)) ∧
    (IsEigenvalue A z → ∀ p, HasNilpotentHeight A z p →
      ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A z,
      (∀ k j : ℕ, j ≤ p+k → omegaC ((shifted A z^(p+k)) v) w =
        (-z^2)^j*omegaC ((shifted A z^(p+k-j)) v) ((shifted A z⁻¹^j) w)) ∧
      omegaC ((shifted A z^p) v) w = (-z^2)^p*omegaC v ((shifted A z⁻¹^p) w) ∧
      (∀ k j : ℕ, p < k+j → omegaC ((shifted A z^(k)) v) ((shifted A z⁻¹^j) w) = 0)) :=
  X4CZG.main A hA z hz0
