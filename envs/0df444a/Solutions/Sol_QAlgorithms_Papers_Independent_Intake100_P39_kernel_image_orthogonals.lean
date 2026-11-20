-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P39.kernel_image_orthogonals
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T12:02:22.039043+00:00
-- url     : https://prove2.me/submissions/e8f156da-9bb7-459c-a740-70c6195f7ac0

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

theorem AuxK_add_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v + v') w = omegaC v w + omegaC v' w := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_add_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w + w') = omegaC v w + omegaC v w' := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_smul_l {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC (c • v) w = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_smul_r {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC v (c • w) = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_zero_l {n : ℕ} (w : Coord n → ℂ) : omegaC 0 w = 0 := by simp [omegaC]

theorem AuxK_zero_r {n : ℕ} (v : Coord n → ℂ) : omegaC v 0 = 0 := by simp [omegaC]

theorem AuxK_eq {n : ℕ} (v w : Coord n → ℂ) :
    omegaC v w = -(v ⬝ᵥ (complexify (canonicalJ n) *ᵥ w)) := by
  have h1 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inl i) = -w (Sum.inr i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  have h2 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inr i) = w (Sum.inl i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2]
  rw [omegaC, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_inv {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) (v w : Coord n → ℂ) :
    omegaC (complexify A *ᵥ v) (complexify A *ᵥ w) = omegaC v w := by
  have hC : (complexify A)ᵀ * complexify (canonicalJ n) * complexify A = complexify (canonicalJ n) := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  rw [AuxK_eq, AuxK_eq]
  conv_rhs => rw [← hC]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem AuxK_sh {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : Coord n → ℂ) :
    complexify A *ᵥ v = shifted A z v + z • v := by
  simp [shifted, Matrix.toLin'_apply]

theorem AuxK_sub_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v - v') w = omegaC v w - omegaC v' w := by
  simp only [omegaC, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_sub_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w - w') = omegaC v w - omegaC v w' := by
  simp only [omegaC, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxK_J2 (n : ℕ) : complexify (canonicalJ n) * complexify (canonicalJ n) = -1 := by
  have hR : canonicalJ n * canonicalJ n = -1 := by
    rw [canonicalJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have := congrArg (Matrix.map · Complex.ofRealHom) hR
  rw [Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg Complex.ofRealHom a),
    Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem AuxK_nd {n : ℕ} (x : Coord n → ℂ) (h : ∀ u, omegaC x u = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [omegaC, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [omegaC, Pi.single_apply] using this

theorem _root_.solution {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : z ≠ 0) (j : ℕ) (v : CVec n) :
    v ∈ LinearMap.ker (shifted A z ^ j) ↔
      OrthogonalC (LinearMap.range (shifted A z⁻¹ ^ j)) v := by
  set Ac := complexify A with hAc
  set Jc := complexify (canonicalJ n) with hJc
  have hC : Acᵀ * Jc * Ac = Jc := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  set Linv : Matrix (Coord n) (Coord n) ℂ := -(Jc * Acᵀ * Jc) with hLdef
  have hL : Linv * Ac = 1 := by
    have e : Jc * Acᵀ * Jc * Ac = Jc * (Acᵀ * Jc * Ac) := by simp only [Matrix.mul_assoc]
    rw [hLdef, neg_mul, e, hC, AuxK_J2, neg_neg]
  have hR : Ac * Linv = 1 := mul_eq_one_comm.1 hL
  set Lc : Module.End ℂ (Coord n → ℂ) := Matrix.toLin' Linv with hLc
  set Ap : Module.End ℂ (Coord n → ℂ) := Matrix.toLin' Ac with hAp
  have hLA : Lc * Ap = 1 := by rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hL, Matrix.toLin'_one]; rfl
  have hAL : Ap * Lc = 1 := by rw [hLc, hAp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hR, Matrix.toLin'_one]; rfl
  have hN : ∀ c : ℂ, shifted A c = Ap - c • 1 := fun c => rfl
  have adj0 : ∀ x y, omegaC x (Ap y) = omegaC (Lc x) y := by
    intro x y
    rw [← AuxK_inv A hA (Lc x) y]
    show omegaC x (Ac *ᵥ y) = omegaC (Ac *ᵥ (Linv *ᵥ x)) (Ac *ᵥ y)
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  set S : Module.End ℂ (Coord n → ℂ) := Lc - z⁻¹ • 1 with hS
  have adj1 : ∀ x u, omegaC x (shifted A z⁻¹ u) = omegaC (S x) u := by
    intro x u
    rw [hN, hS]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [AuxK_sub_r, AuxK_sub_l, AuxK_smul_r, AuxK_smul_l, adj0]
  have adjj : ∀ k : ℕ, ∀ x u, omegaC x ((shifted A z⁻¹ ^ k) u) = omegaC ((S ^ k) x) u := by
    intro k
    induction k with
    | zero => intro x u; simp
    | succ k ih =>
      intro x u
      rw [pow_succ, Module.End.mul_apply, ih, adj1, pow_succ', Module.End.mul_apply]
  set U : Module.End ℂ (Coord n → ℂ) := (-z⁻¹) • Lc with hU
  set V : Module.End ℂ (Coord n → ℂ) := (-z) • Ap with hV
  have hSU : S = U * shifted A z := by
    rw [hS, hU, hN, smul_mul_assoc, mul_sub, hLA, mul_smul_comm, mul_one, smul_sub, smul_smul,
      neg_mul, inv_mul_cancel₀ hz]
    module
  have hUN : U * shifted A z = shifted A z * U := by
    rw [hU, hN, smul_mul_assoc, mul_sub, hLA, mul_smul_comm, mul_one, mul_smul_comm, sub_mul, hAL,
      smul_mul_assoc, one_mul]
  have hVU : V * U = 1 := by
    rw [hV, hU, smul_mul_assoc, mul_smul_comm, hAL, smul_smul, mul_neg, neg_mul, neg_neg,
      mul_inv_cancel₀ hz, one_smul]
  have hUV : U * V = 1 := by
    rw [hV, hU, smul_mul_assoc, mul_smul_comm, hLA, smul_smul, mul_neg, neg_mul, neg_neg,
      inv_mul_cancel₀ hz, one_smul]
  have hSj : S ^ j = U ^ j * shifted A z ^ j := by rw [hSU, (Commute.mul_pow hUN)]
  have hVUj : V ^ j * U ^ j = 1 := by
    rw [← (Commute.mul_pow (show Commute V U from hVU.trans hUV.symm)), hVU, one_pow]
  have iff1 : (S ^ j) v = 0 ↔ (shifted A z ^ j) v = 0 := by
    constructor
    · intro h
      have : (V ^ j * U ^ j) ((shifted A z ^ j) v) = 0 := by
        rw [Module.End.mul_apply, ← Module.End.mul_apply (U ^ j), ← hSj, h, map_zero]
      rwa [hVUj, Module.End.one_apply] at this
    · intro h
      rw [hSj, Module.End.mul_apply, h, map_zero]
  rw [LinearMap.mem_ker, ← iff1]
  constructor
  · rintro h w ⟨u, rfl⟩
    rw [adjj, h, AuxK_zero_l]
  · intro h
    apply AuxK_nd
    intro u
    rw [← adjj]
    exact h _ ⟨u, rfl⟩

end QAlgorithms.Papers.Independent.Intake100.P39
