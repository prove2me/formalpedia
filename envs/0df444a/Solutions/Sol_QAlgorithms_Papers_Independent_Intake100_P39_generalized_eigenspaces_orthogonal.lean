-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P39.generalized_eigenspaces_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:59:59.060582+00:00
-- url     : https://prove2.me/submissions/2e2b7bb6-771f-4080-9986-e84003df7e09

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

theorem AuxG_add_l {n : ℕ} (v v' w : Coord n → ℂ) : omegaC (v + v') w = omegaC v w + omegaC v' w := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxG_add_r {n : ℕ} (v w w' : Coord n → ℂ) : omegaC v (w + w') = omegaC v w + omegaC v w' := by
  simp only [omegaC, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxG_smul_l {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC (c • v) w = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxG_smul_r {n : ℕ} (c : ℂ) (v w : Coord n → ℂ) : omegaC v (c • w) = c * omegaC v w := by
  simp only [omegaC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxG_zero_l {n : ℕ} (w : Coord n → ℂ) : omegaC 0 w = 0 := by simp [omegaC]

theorem AuxG_zero_r {n : ℕ} (v : Coord n → ℂ) : omegaC v 0 = 0 := by simp [omegaC]

theorem AuxG_eq {n : ℕ} (v w : Coord n → ℂ) :
    omegaC v w = -(v ⬝ᵥ (complexify (canonicalJ n) *ᵥ w)) := by
  have h1 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inl i) = -w (Sum.inr i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  have h2 : ∀ i, (complexify (canonicalJ n) *ᵥ w) (Sum.inr i) = w (Sum.inl i) := by
    intro i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, canonicalJ, complexify, Matrix.one_apply, apply_ite]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2]
  rw [omegaC, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem AuxG_inv {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) (v w : Coord n → ℂ) :
    omegaC (complexify A *ᵥ v) (complexify A *ᵥ w) = omegaC v w := by
  have hC : (complexify A)ᵀ * complexify (canonicalJ n) * complexify A = complexify (canonicalJ n) := by
    have := congrArg (Matrix.map · Complex.ofRealHom) hA
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  rw [AuxG_eq, AuxG_eq]
  conv_rhs => rw [← hC]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem AuxG_sh {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (v : Coord n → ℂ) :
    complexify A *ᵥ v = shifted A z v + z • v := by
  simp [shifted, Matrix.toLin'_apply]

theorem _root_.solution {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z t : ℂ) (hzt : z * t ≠ 1)
    (v w : CVec n) (hv : v ∈ generalizedSpace A z) (hw : w ∈ generalizedSpace A t) :
    omegaC v w = 0 := by
  have key : ∀ p q : ℕ, ∀ v w : Coord n → ℂ, (shifted A z ^ p) v = 0 → (shifted A t ^ q) w = 0 →
      omegaC v w = 0 := by
    intro p
    induction p with
    | zero => intro q v w hv _; simp at hv; rw [hv, AuxG_zero_l]
    | succ p ihp =>
      intro q
      induction q with
      | zero => intro v w _ hw; simp at hw; rw [hw, AuxG_zero_r]
      | succ q ihq =>
        intro v w hv hw
        have hv' : (shifted A z ^ p) (shifted A z v) = 0 := by
          rw [← Module.End.mul_apply, ← pow_succ]; exact hv
        have hw' : (shifted A t ^ q) (shifted A t w) = 0 := by
          rw [← Module.End.mul_apply, ← pow_succ]; exact hw
        have e1 := ihp (q+1) (shifted A z v) w hv' hw
        have e2 := ihp q (shifted A z v) (shifted A t w) hv' hw'
        have e3 := ihq v (shifted A t w) hv hw'
        have e : omegaC v w = z * t * omegaC v w := by
          conv_lhs => rw [← AuxG_inv A hA v w, AuxG_sh A z v, AuxG_sh A t w]
          rw [AuxG_add_l, AuxG_add_r, AuxG_add_r, AuxG_smul_l, AuxG_smul_l, AuxG_smul_r, AuxG_smul_r,
            e1, e2, e3]
          ring
        have : (1 - z * t) * omegaC v w = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hzt))
  exact key (2*n) (2*n) v w hv hw

end QAlgorithms.Papers.Independent.Intake100.P39
