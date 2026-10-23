-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.generalized_quotient_pairing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:58:54.00092+00:00
-- url     : https://prove2.me/submissions/85a6c645-8a44-4bbc-8662-823e16e42dcc

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

lemma orth (A : GroupedRealMatrix n) (hA : IsSymplectic A) (z u : ℂ) (hz0 : z ≠ 0)
    (hzu : z*u ≠ 1) :
    ∀ v ∈ generalizedSpace A z, ∀ w ∈ generalizedSpace A u, omegaC v w = 0 := by
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

lemma oc_add_l (x x' y : Coord n → ℂ) : omegaC (x + x') y = omegaC x y + omegaC x' y := by
  unfold omegaC; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

lemma oc_add_r (x y y' : Coord n → ℂ) : omegaC x (y + y') = omegaC x y + omegaC x y' := by
  unfold omegaC; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

lemma oc_zero_r (x : Coord n → ℂ) : omegaC x 0 = 0 := by simp [omegaC]

lemma oc_anti (x y : Coord n → ℂ) : omegaC x y = -omegaC y x := by
  unfold omegaC; rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; ring

lemma gen_eq (A : GroupedRealMatrix n) (μ : ℂ) :
    Module.End.maxGenEigenspace (Matrix.toLin' (complexify A) : Module.End ℂ (Coord n → ℂ)) μ = generalizedSpace A μ := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat]
  have : Module.finrank ℂ (Coord n → ℂ) = 2 * n := by
    simp [Module.finrank_fintype_fun_eq_card]; ring
  rw [this]; rfl

lemma ortho_all (A : GroupedRealMatrix n) (hA : IsSymplectic A) (z : ℂ) (hz0 : z ≠ 0)
    (x : Coord n → ℂ) (hx : x ∈ generalizedSpace A z)
    (h : ∀ w ∈ generalizedSpace A z⁻¹, omegaC x w = 0) : x = 0 := by
  apply nondeg
  intro u
  have hu : u ∈ ⨆ μ, Module.End.maxGenEigenspace (Matrix.toLin' (complexify A) : Module.End ℂ (Coord n → ℂ)) μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun u => omegaC x u = 0) hu ?_ (oc_zero_r x) ?_
  · intro μ y hy
    rw [gen_eq] at hy
    by_cases hμ : μ = z⁻¹
    · subst hμ; exact h y hy
    · refine orth A hA z μ hz0 ?_ x hx y hy
      intro h1; apply hμ; exact eq_inv_of_mul_eq_one_right h1
  · intro y y' h1 h2
    rw [oc_add_r, h1, h2, add_zero]

lemma pow_mem (A : GroupedRealMatrix n) (c u : ℂ) (j : ℕ) (y : Coord n → ℂ)
    (hy : y ∈ generalizedSpace A u) : (shifted A c ^ j) y ∈ generalizedSpace A u := by
  induction j with
  | zero => simpa using hy
  | succ j ih => rw [pow_succ_apply]; exact inv_mem A c u _ ih

lemma comm_pow2 (A : GroupedRealMatrix n) (c : ℂ) (i j : ℕ) (y : Coord n → ℂ) :
    (shifted A c ^ i) ((complexify A ^ j) *ᵥ y) = (complexify A ^ j) *ᵥ ((shifted A c ^ i) y) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ_apply, ih, comm_pow, ← pow_succ_apply]

lemma inj_pow (A : GroupedRealMatrix n) (hA : IsSymplectic A) (j : ℕ) (x : Coord n → ℂ)
    (h : (complexify A ^ j) *ᵥ x = 0) : x = 0 := by
  have hd : (complexify A ^ j).det ≠ 0 := by
    rw [Matrix.det_pow, cx_eq]
    change ((Complex.ofRealHom).mapMatrix A).det ^ j ≠ 0
    rw [← RingHom.map_det]
    exact pow_ne_zero _ (by simpa using det_ne A hA)
  have := congrArg (fun y => (complexify A ^ j)⁻¹ *ᵥ y) h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hd), Matrix.one_mulVec,
    Matrix.mulVec_zero] using this

lemma surj_pow_on (A : GroupedRealMatrix n) (u : ℂ) (hu : u ≠ 0) (j : ℕ) (w : Coord n → ℂ)
    (hw : w ∈ generalizedSpace A u) :
    ∃ y ∈ generalizedSpace A u, (complexify A ^ j) *ᵥ y = w := by
  induction j generalizing w with
  | zero => exact ⟨w, hw, by simp⟩
  | succ j ih =>
    obtain ⟨y1, hy1, rfl⟩ := ih w hw
    obtain ⟨y, hy, hyy⟩ := surj_on A 0 u (Ne.symm hu) y1 hy1
    rw [sh_apply, zero_smul, sub_zero] at hyy
    exact ⟨y, hy, by rw [pow_succ, ← Matrix.mulVec_mulVec, hyy]⟩

theorem main (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : IsEigenvalue A z) (hz0 : z ≠ 0) (j : ℕ) (hj : 0 < j) :
    ∃ Q : GeneralizedQuotient A z j →ₗ[ℂ] GeneralizedQuotient A z⁻¹ j →ₗ[ℂ] ℂ,
      (∀ v : generalizedSpace A z, ∀ w : generalizedSpace A z⁻¹,
        Q ((restrictedKernel A z j).mkQ v) ((restrictedKernel A z⁻¹ j).mkQ w) =
          omegaC ((shifted A z^j) v.val) w.val) ∧
      (∀ v, (∀ w, Q v w = 0) → v = 0) ∧ (∀ w, (∀ v, Q v w = 0) → w = 0) := by
  set B : generalizedSpace A z →ₗ[ℂ] generalizedSpace A z⁻¹ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun v w => omegaC ((shifted A z ^ j) v.val) w.val)
      (fun v v' w => by simp [oc_add_l])
      (fun c v w => by simp [oc_smul_l])
      (fun v w w' => by simp [oc_add_r])
      (fun c v w => by simp [oc_smul_r]) with hB
  have key : ∀ (v : Coord n → ℂ) (w : Coord n → ℂ), (shifted A z⁻¹ ^ j) w = 0 →
      omegaC ((shifted A z ^ j) v) w = 0 := by
    intro v w hw
    obtain ⟨y, rfl⟩ := surj A hA j w
    rw [comm_pow2] at hw
    rw [adj_pow A hA z hz0, inj_pow A hA j _ hw, oc_zero_r, mul_zero]
  have hM : restrictedKernel A z j ≤ LinearMap.ker B := by
    intro v hv
    rw [LinearMap.mem_ker]
    ext w
    have : (shifted A z ^ j) v.val = 0 := hv
    simp [hB, this, oc_zero_l]
  have hN : restrictedKernel A z⁻¹ j ≤ LinearMap.ker B.flip := by
    intro w hw
    rw [LinearMap.mem_ker]
    ext v
    have : (shifted A z⁻¹ ^ j) w.val = 0 := hw
    simp [hB, key v.val w.val this]
  refine ⟨B.liftQ₂ _ _ hM hN, ?_, ?_, ?_⟩
  · intro v w
    rfl
  · intro v hv
    induction v using Submodule.Quotient.induction_on with
    | H v =>
    rw [Submodule.Quotient.mk_eq_zero]
    have h0 : (shifted A z ^ j) v.val = 0 := by
      refine ortho_all A hA z hz0 _ (pow_mem A z z j v.val v.2) ?_
      intro w hw
      exact hv (Submodule.Quotient.mk ⟨w, hw⟩)
    exact h0
  · intro w hw
    induction w using Submodule.Quotient.induction_on with
    | H w =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hz1 : z⁻¹ ≠ 0 := inv_ne_zero hz0
    obtain ⟨y, hy, hyw⟩ := surj_pow_on A z⁻¹ hz1 j w.val w.2
    have h1 : ∀ v ∈ generalizedSpace A z, omegaC v ((shifted A z⁻¹ ^ j) y) = 0 := by
      intro v hv
      have := hw (Submodule.Quotient.mk ⟨v, hv⟩)
      change omegaC ((shifted A z ^ j) v) w.val = 0 at this
      rw [← hyw, adj_pow A hA z hz0] at this
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (neg_ne_zero.2 hz0))
    have h2 : (shifted A z⁻¹ ^ j) y = 0 := by
      refine ortho_all A hA z⁻¹ hz1 _ (pow_mem A z⁻¹ z⁻¹ j y hy) ?_
      intro v hv
      rw [inv_inv] at hv
      rw [oc_anti, h1 v hv, neg_zero]
    change (shifted A z⁻¹ ^ j) w.val = 0
    rw [← hyw, comm_pow2, h2, Matrix.mulVec_zero]

end X4CZG

theorem solution {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : IsEigenvalue A z) (hz0 : z ≠ 0) (j : ℕ) (hj : 0 < j) :
    ∃ Q : GeneralizedQuotient A z j →ₗ[ℂ] GeneralizedQuotient A z⁻¹ j →ₗ[ℂ] ℂ,
      (∀ v : generalizedSpace A z, ∀ w : generalizedSpace A z⁻¹,
        Q ((restrictedKernel A z j).mkQ v) ((restrictedKernel A z⁻¹ j).mkQ w) =
          omegaC ((shifted A z^j) v.val) w.val) ∧
      (∀ v, (∀ w, Q v w = 0) → v = 0) ∧ (∀ w, (∀ v, Q v w = 0) → w = 0) :=
  X4CZG.main A hA z hz hz0 j hj
