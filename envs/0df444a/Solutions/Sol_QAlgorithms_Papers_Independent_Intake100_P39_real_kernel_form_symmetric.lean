-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P39.real_kernel_form_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T12:04:01.784126+00:00
-- url     : https://prove2.me/submissions/64ffea78-af42-4b13-9e08-f9b310336879

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39
noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

theorem AuxR_add_l {n : ℕ} (v v' w : Coord n → ℝ) : omegaR (v + v') w = omegaR v w + omegaR v' w := by
  simp only [omegaR, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_sub_l {n : ℕ} (v v' w : Coord n → ℝ) : omegaR (v - v') w = omegaR v w - omegaR v' w := by
  simp only [omegaR, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_sub_r {n : ℕ} (v w w' : Coord n → ℝ) : omegaR v (w - w') = omegaR v w - omegaR v w' := by
  simp only [omegaR, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_smul_l {n : ℕ} (c : ℝ) (v w : Coord n → ℝ) : omegaR (c • v) w = c * omegaR v w := by
  simp only [omegaR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_smul_r {n : ℕ} (c : ℝ) (v w : Coord n → ℝ) : omegaR v (c • w) = c * omegaR v w := by
  simp only [omegaR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_skew {n : ℕ} (v w : Coord n → ℝ) : omegaR w v = -omegaR v w := by
  simp only [omegaR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_eq {n : ℕ} (v w : Coord n → ℝ) :
    omegaR v w = -(v ⬝ᵥ (canonicalJ n *ᵥ w)) := by
  have h1 : ∀ i, (canonicalJ n *ᵥ w) (Sum.inl i) = -w (Sum.inr i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, Matrix.one_apply, apply_ite]
  have h2 : ∀ i, (canonicalJ n *ᵥ w) (Sum.inr i) = w (Sum.inl i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, Matrix.one_apply, apply_ite]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2]
  rw [omegaR, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxR_inv {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) (v w : Coord n → ℝ) :
    omegaR (A *ᵥ v) (A *ᵥ w) = omegaR v w := by
  have hC : Aᵀ * canonicalJ n * A = canonicalJ n := hA
  rw [AuxR_eq, AuxR_eq]
  conv_rhs => rw [← hC]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem AuxR_J2 (n : ℕ) : canonicalJ n * canonicalJ n = -1 := by
  rw [canonicalJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem _root_.solution {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (a : ℝ) (ha : a = 1 ∨ a = -1) (k : ℕ) (hk : 0 < k)
    (v w : RVec n) (hv : (realShift A a ^ (2 * k)) v = 0)
    (hw : (realShift A a ^ (2 * k)) w = 0) :
    realQ A a k v w = realQ A a k w v := by
  have haa : a * a = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hC : Aᵀ * canonicalJ n * A = canonicalJ n := hA
  set L : GroupedRealMatrix n := -(canonicalJ n * Aᵀ * canonicalJ n) with hLdef
  have hL : L * A = 1 := by
    have e : canonicalJ n * Aᵀ * canonicalJ n * A = canonicalJ n * (Aᵀ * canonicalJ n * A) := by
      simp only [Matrix.mul_assoc]
    rw [hLdef, neg_mul, e, hC, AuxR_J2, neg_neg]
  have hR : A * L = 1 := mul_eq_one_comm.1 hL
  set Lc : Module.End ℝ (Coord n → ℝ) := Matrix.toLin' L with hLc
  set Ap : Module.End ℝ (Coord n → ℝ) := Matrix.toLin' A with hAp
  have hLA : Lc * Ap = 1 := by
    rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hL, Matrix.toLin'_one]; rfl
  have hAL : Ap * Lc = 1 := by
    rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hR, Matrix.toLin'_one]; rfl
  have hN : realShift A a = Ap - a • 1 := rfl
  have adj0 : ∀ x y, omegaR x (Ap y) = omegaR (Lc x) y := by
    intro x y
    rw [← AuxR_inv A hA (Lc x) y]
    show omegaR x (A *ᵥ y) = omegaR (A *ᵥ (L *ᵥ x)) (A *ᵥ y)
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  set S : Module.End ℝ (Coord n → ℝ) := Lc - a • 1 with hS
  have adj1 : ∀ x u, omegaR x (realShift A a u) = omegaR (S x) u := by
    intro x u
    rw [hN, hS]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [AuxR_sub_r, AuxR_sub_l, AuxR_smul_r, AuxR_smul_l, adj0]
  have adjj : ∀ m : ℕ, ∀ x u, omegaR x ((realShift A a ^ m) u) = omegaR ((S ^ m) x) u := by
    intro m
    induction m with
    | zero => intro x u; simp
    | succ m ih =>
      intro x u
      rw [pow_succ, Module.End.mul_apply, ih, adj1, pow_succ', Module.End.mul_apply]
  set U : Module.End ℝ (Coord n → ℝ) := (-a) • Lc with hU
  have hSU : S = U * realShift A a := by
    rw [hS, hU, hN, smul_mul_assoc, mul_sub, hLA, mul_smul_comm, mul_one, smul_sub, smul_smul,
      neg_mul, haa]
    module
  have hUN : U * realShift A a = realShift A a * U := by
    rw [hU, hN, smul_mul_assoc, mul_sub, hLA, mul_smul_comm, mul_one, mul_smul_comm, sub_mul, hAL,
      smul_mul_assoc, one_mul]
  have hSm : ∀ m x, (S ^ m) x = (U ^ m) ((realShift A a ^ m) x) := by
    intro m x
    rw [hSU, Commute.mul_pow hUN, Module.End.mul_apply]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set y := (realShift A a ^ (2*k'+1)) v with hy
  have hNy : realShift A a y = 0 := by
    rw [hy, ← Module.End.mul_apply, ← pow_succ']
    have e : 2*k'+1+1 = 2*(k'+1) := by ring
    rw [e]; exact hv
  have hAy : Ap y = a • y := by
    have := hNy; rw [hN] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have hLy : Lc y = a • y := by
    have h1 : y = Lc (Ap y) := by rw [← Module.End.mul_apply, hLA, Module.End.one_apply]
    rw [hAy, map_smul] at h1
    calc Lc y = (a * a) • Lc y := by rw [haa, one_smul]
      _ = a • (a • Lc y) := by rw [smul_smul]
      _ = a • y := by rw [← h1]
  have hUy : U y = -y := by
    rw [hU, LinearMap.smul_apply, hLy, smul_smul, neg_mul, haa, neg_one_smul]
  have hUmy : ∀ m : ℕ, (U ^ m) y = ((-1 : ℝ) ^ m) • y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hUy, pow_succ', smul_neg,
        neg_one_mul, neg_smul]
  have q1 : omegaR ((realShift A a ^ (k'+1)) v) ((realShift A a ^ k') w) = (-1 : ℝ)^k' * omegaR y w := by
    rw [adjj, hSm, ← Module.End.mul_apply (realShift A a ^ k'), ← pow_add,
      show k' + (k'+1) = 2*k'+1 by ring, hUmy, AuxR_smul_l]
  have q2 : omegaR ((realShift A a ^ k') v) ((realShift A a ^ (k'+1)) w) =
      (-1 : ℝ)^(k'+1) * omegaR y w := by
    rw [adjj, hSm, ← Module.End.mul_apply (realShift A a ^ (k'+1)), ← pow_add,
      show k' + 1 + k' = 2*k'+1 by ring, hUmy, AuxR_smul_l]
  unfold realQ
  rw [show k' + 1 - 1 = k' by omega, q1, AuxR_skew ((realShift A a ^ k') v) ((realShift A a ^ (k'+1)) w), q2, pow_succ]
  ring

end QAlgorithms.Papers.Independent.Intake100.P39
