-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_eigenspaces_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:54:31.801255+00:00
-- url     : https://prove2.me/submissions/43794ce6-3baf-4fcb-af60-54ef3e6ae978

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

lemma oc_neg_l (x y : Coord n → ℂ) : omegaC (-x) y = -omegaC x y := by
  rw [show -x = (-1:ℂ) • x by simp, oc_smul_l]; ring

/-- Adjoint relation: ω(Lx, Ay) = -z ω(x, My). -/
lemma adj (A : GroupedRealMatrix n) (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0)
    (x y : Coord n → ℂ) :
    omegaC (shifted A z x) (complexify A *ᵥ y) = -z * omegaC x (shifted A z⁻¹ y) := by
  simp only [sh_apply, oc_sub_l, oc_sub_r, oc_smul_l, oc_smul_r, oc_inv A hA]
  field_simp
  ring

lemma comm_sh (A : GroupedRealMatrix n) (c : ℂ) (y : Coord n → ℂ) :
    shifted A c (complexify A *ᵥ y) = complexify A *ᵥ (shifted A c y) := by
  simp only [sh_apply, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

lemma Apow (A : GroupedRealMatrix n) (j : ℕ) (y : Coord n → ℂ) :
    (Matrix.toLin' (complexify A) ^ j) y = (complexify A ^ j) *ᵥ y := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [pow_succ_apply, ih, pow_succ', Matrix.toLin'_apply, Matrix.mulVec_mulVec]

lemma comm_pow (A : GroupedRealMatrix n) (c : ℂ) (j : ℕ) (y : Coord n → ℂ) :
    shifted A c ((complexify A ^ j) *ᵥ y) = (complexify A ^ j) *ᵥ (shifted A c y) := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, comm_sh, ih, Matrix.mulVec_mulVec]

lemma adj_pow (A : GroupedRealMatrix n) (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0) (j : ℕ)
    (x y : Coord n → ℂ) :
    omegaC ((shifted A z ^ j) x) ((complexify A ^ j) *ᵥ y) =
      (-z) ^ j * omegaC x ((shifted A z⁻¹ ^ j) y) := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [pow_succ_apply, pow_succ' (complexify A), ← Matrix.mulVec_mulVec, adj A hA z hz0, comm_pow,
      ih, show (shifted A z⁻¹ ^ j) (shifted A z⁻¹ y) = (shifted A z⁻¹ ^ (j+1)) y by
      rw [pow_succ, Module.End.mul_apply]]
    ring

lemma nondeg (x : Coord n → ℂ) (h : ∀ u, omegaC x u = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [omegaC, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [omegaC, Pi.single_apply] using this

lemma symp_iff (A : GroupedRealMatrix n) :
    IsSymplectic A ↔ Aᵀ * omegaMatrix n * A = omegaMatrix n := by
  unfold IsSymplectic
  rw [J_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

lemma det_ne (A : GroupedRealMatrix n) (h : IsSymplectic A) : A.det ≠ 0 := by
  rw [symp_iff] at h
  have hO : (omegaMatrix n).det ≠ 0 := by
    have : omegaMatrix n * omegaMatrix n = -1 := by
      unfold omegaMatrix; rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
      simp
    intro h0
    have := congrArg Matrix.det this
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg, Matrix.det_one] at this
    simp at this
  intro h0
  apply hO
  rw [← h, Matrix.det_mul, h0, mul_zero]

lemma surj (A : GroupedRealMatrix n) (hA : IsSymplectic A) (j : ℕ) (u : Coord n → ℂ) :
    ∃ y, (complexify A ^ j) *ᵥ y = u := by
  have hd : (complexify A ^ j).det ≠ 0 := by
    rw [Matrix.det_pow, cx_eq]
    change ((Complex.ofRealHom).mapMatrix A).det ^ j ≠ 0
    rw [← RingHom.map_det]
    exact pow_ne_zero _ (by simpa using det_ne A hA)
  refine ⟨(complexify A ^ j)⁻¹ *ᵥ u, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mulVec]

lemma z_ne (A : GroupedRealMatrix n) (hA : IsSymplectic A) (z : ℂ) (hz : IsEigenvalue A z) :
    z ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv, h⟩ := hz
  rw [sh_apply, zero_smul, sub_zero] at h
  apply hv
  obtain ⟨y, hy⟩ := surj A hA 0 v
  have hd : (complexify A).det ≠ 0 := by
    rw [cx_eq]; change ((Complex.ofRealHom).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]; simpa using det_ne A hA
  have := congrArg (fun x => (complexify A)⁻¹ *ᵥ x) h
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hd), Matrix.one_mulVec,
    Matrix.mulVec_zero] at this
  exact this

lemma sh_eq (A : GroupedRealMatrix n) (c : ℂ) :
    shifted A c = Matrix.toLin' (complexify A) - c • 1 := rfl

lemma sh_comm (A : GroupedRealMatrix n) (c d : ℂ) : Commute (shifted A c) (shifted A d) := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, sh_apply, Matrix.mulVec_sub, Matrix.mulVec_smul]
  module

lemma pow_eig (S : Module.End ℂ (Coord n → ℂ)) (a : ℂ) (y : Coord n → ℂ) (h : S y = a • y) (k : ℕ) :
    (S ^ k) y = a ^ k • y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ_apply, ih, map_smul, h, smul_smul, pow_succ, mul_comm]

lemma inv_mem (A : GroupedRealMatrix n) (c u : ℂ) (y : Coord n → ℂ) (hy : y ∈ generalizedSpace A u) :
    shifted A c y ∈ generalizedSpace A u := by
  unfold generalizedSpace at *
  rw [LinearMap.mem_ker] at *
  rw [← Module.End.mul_apply, ((sh_comm A c u).pow_right _).symm.eq, Module.End.mul_apply, hy, map_zero]

lemma surj_on (A : GroupedRealMatrix n) (c u : ℂ) (hcu : c ≠ u) (w : Coord n → ℂ)
    (hw : w ∈ generalizedSpace A u) :
    ∃ y ∈ generalizedSpace A u, shifted A c y = w := by
  set E := generalizedSpace A u
  set Mr : E →ₗ[ℂ] E := (shifted A c).restrict (fun y hy => inv_mem A c u y hy)
  have hinj : Function.Injective Mr := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨y, hy⟩ hk
    rw [LinearMap.mem_ker] at hk
    have h0 : shifted A c y = 0 := congrArg Subtype.val hk
    have h1 : shifted A u y = (c - u) • y := by
      rw [sh_apply] at h0 ⊢
      rw [sub_smul, ← sub_eq_zero.1 h0]
    have h2 := pow_eig _ _ y h1 (2*n)
    have hy' : (shifted A u ^ (2*n)) y = 0 := hy
    rw [hy'] at h2
    have := (smul_eq_zero.1 h2.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.2 hcu))
    ext1; exact this
  obtain ⟨⟨y, hy⟩, hyw⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨w, hw⟩
  exact ⟨y, hy, congrArg Subtype.val hyw⟩

theorem main (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z u : ℂ) (hz : IsEigenvalue A z)
    (hu : IsEigenvalue A u) (hzu : z*u ≠ 1) :
    ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A u, omegaC v w = 0 := by
  have hz0 := z_ne A hA z hz
  have hcu : z⁻¹ ≠ u := by
    intro h; apply hzu; rw [← h, mul_inv_cancel₀ hz0]
  have key : ∀ k : ℕ, ∀ v, (shifted A z ^ k) v = 0 →
      ∀ w ∈ generalizedSpace A u, omegaC v w = 0 := by
    intro k
    induction k with
    | zero => intro v hv w _; simp at hv; rw [hv, oc_zero_l]
    | succ k ih =>
      intro v hv w hw
      have hLv : (shifted A z ^ k) (shifted A z v) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ]; exact hv
      obtain ⟨y, hy, rfl⟩ := surj_on A z⁻¹ u hcu w hw
      have hAy : complexify A *ᵥ y ∈ generalizedSpace A u := by
        have h1 := inv_mem A 0 u y hy
        rw [sh_apply, zero_smul, sub_zero] at h1; exact h1
      have := adj A hA z hz0 v y
      rw [ih _ hLv _ hAy] at this
      exact ((mul_eq_zero.1 this.symm).resolve_left (neg_ne_zero.2 hz0))
  intro v hv w hw
  exact key (2*n) v hv w hw

end X4CZG

theorem solution {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z u : ℂ) (hz : IsEigenvalue A z)
    (hu : IsEigenvalue A u) (hzu : z*u ≠ 1) :
    ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A u, omegaC v w = 0 :=
  X4CZG.main A hA z u hz hu hzu
