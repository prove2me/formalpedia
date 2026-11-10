-- Prove2me | solution 1 for ShendeQSD.Synthesis.demux_single_rot
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:13:42.800507+00:00
-- url     : https://prove2.me/submissions/af35ac19-8b81-4cf2-8646-44721235379e

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_rz
import Definitions.Def_ShendeQSD_Synthesis_ry

open scoped Kronecker

namespace Aux_ShendeDemux

open QAlgorithms ShendeQSD.Synthesis

def P0 : Matrix Bool Bool ℂ := Matrix.diagonal fun c => if c then 0 else 1
def P1 : Matrix Bool Bool ℂ := Matrix.diagonal fun c => if c then 1 else 0

theorem cx_eq : cnot.submatrix Prod.swap Prod.swap
    = (1 : Matrix Bool Bool ℂ) ⊗ₖ P0 + pauliX ⊗ₖ P1 := by
  ext ⟨a, c⟩ ⟨b, d⟩
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [cnot, pauliX, P0, P1, Matrix.kronecker_apply, Matrix.one_apply]

theorem mux_eq (R : ℝ → Matrix Bool Bool ℂ) (θ : Bool → ℝ) :
    muxRot R θ = R (θ false) ⊗ₖ P0 + R (θ true) ⊗ₖ P1 := by
  ext ⟨a, c⟩ ⟨b, d⟩
  cases c <;> cases d <;> simp [muxRot, P0, P1, Matrix.kronecker_apply]

theorem p00 : P0 * P0 = P0 := by
  ext i j; cases i <;> cases j <;> simp [P0]
theorem p11 : P1 * P1 = P1 := by
  ext i j; cases i <;> cases j <;> simp [P1]
theorem p01 : P0 * P1 = 0 := by
  ext i j; cases i <;> cases j <;> simp [P0, P1]
theorem p10 : P1 * P0 = 0 := by
  ext i j; cases i <;> cases j <;> simp [P0, P1]

theorem prod_eq (A B : Matrix Bool Bool ℂ) :
    ((1 : Matrix Bool Bool ℂ) ⊗ₖ P0 + pauliX ⊗ₖ P1) * (A ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ P0 + pauliX ⊗ₖ P1) * (B ⊗ₖ (1 : Matrix Bool Bool ℂ))
      = (A * B) ⊗ₖ P0 + (pauliX * A * pauliX * B) ⊗ₖ P1 := by
  simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    p00, p11, p01, p10, Matrix.kronecker_zero, add_zero, zero_add]

theorem generic (R : ℝ → Matrix Bool Bool ℂ) (hadd : ∀ a b, R a * R b = R (a + b))
    (hX : ∀ a, pauliX * R a * pauliX = R (-a)) :
    (∀ θ : Bool → ℝ,
      muxRot R θ =
        cnot.submatrix Prod.swap Prod.swap *
          (R ((θ false - θ true) / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap *
          (R ((θ false + θ true) / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ))) ∧
    (∀ a b : ℝ, ∃ θ : Bool → ℝ,
      cnot.submatrix Prod.swap Prod.swap * (R a ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap * (R b ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
        muxRot R θ) := by
  have main : ∀ a b : ℝ,
      cnot.submatrix Prod.swap Prod.swap * (R a ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap * (R b ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
        R (a + b) ⊗ₖ P0 + R (-a + b) ⊗ₖ P1 := by
    intro a b
    rw [cx_eq, prod_eq, hadd, hX, hadd]
  refine ⟨fun θ => ?_, fun a b => ?_⟩
  · rw [main, mux_eq]
    have e1 : (θ false - θ true) / 2 + (θ false + θ true) / 2 = θ false := by ring
    have e2 : -((θ false - θ true) / 2) + (θ false + θ true) / 2 = θ true := by ring
    rw [e1, e2]
  · refine ⟨fun c => if c then b - a else a + b, ?_⟩
    rw [main, mux_eq]
    rw [if_neg Bool.false_ne_true, if_pos rfl, show b - a = -a + b by ring]

theorem rz_add (a b : ℝ) : rz a * rz b = rz (a + b) := by
  ext i j
  cases i <;> cases j <;> simp [rz, Matrix.diagonal_apply, ← Complex.exp_add] <;> ring_nf

theorem rz_X (a : ℝ) : pauliX * rz a * pauliX = rz (-a) := by
  ext i j
  cases i <;> cases j <;>
    simp [rz, pauliX, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply] <;> ring_nf

theorem ry_add (a b : ℝ) : ry a * ry b = ry (a + b) := by
  have e : (a + b) / 2 = a / 2 + b / 2 := by ring
  ext i j
  cases i <;> cases j <;>
    simp [ry, Matrix.mul_apply, Fintype.sum_bool, e, Real.cos_add, Real.sin_add] <;> ring

theorem ry_X (a : ℝ) : pauliX * ry a * pauliX = ry (-a) := by
  have e : -a / 2 = -(a / 2) := by ring
  ext i j
  cases i <;> cases j <;>
    simp [ry, pauliX, Matrix.mul_apply, Fintype.sum_bool, e]

end Aux_ShendeDemux

open QAlgorithms ShendeQSD.Synthesis in
theorem solution (R : ℝ → Matrix Bool Bool ℂ) (hR : R = rz ∨ R = ry) :
    (∀ θ : Bool → ℝ,
      muxRot R θ =
        cnot.submatrix Prod.swap Prod.swap *
          (R ((θ false - θ true) / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap *
          (R ((θ false + θ true) / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ))) ∧
    (∀ a b : ℝ, ∃ θ : Bool → ℝ,
      cnot.submatrix Prod.swap Prod.swap * (R a ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap * (R b ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
        muxRot R θ) := by
  rcases hR with rfl | rfl
  · exact Aux_ShendeDemux.generic rz Aux_ShendeDemux.rz_add Aux_ShendeDemux.rz_X
  · exact Aux_ShendeDemux.generic ry Aux_ShendeDemux.ry_add Aux_ShendeDemux.ry_X
