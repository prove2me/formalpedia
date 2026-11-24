-- Prove2me | solution 1 for P2M_RH_PI_UnitaryGroupMassFormula_UsCost_det_zjH_ne_3b4c561a80972532
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:17.03856+00:00
-- url     : https://prove2.me/submissions/c38829d6-533e-4bd1-a399-520b143f3c5b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section smoothAt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
end smoothAt
section slice
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
private lemma det_one_add_strictLower {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (h : ∀ a b, a ≤ b → M a b = 0) :
    (1 + M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [h _ _ le_rfl]
  · intro i j hij
    have hij' : i < j := hij
    simp [Matrix.one_apply_ne hij'.ne, h i j hij'.le]
private lemma det_one_add_strictUpper' {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (h : ∀ a b, b ≤ a → M a b = 0) :
    (1 + M).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h _ _ le_rfl]
  · intro i j hij
    have hij' : j < i := hij
    simp [Matrix.one_apply_ne hij'.ne', h i j hij'.le]
end slice
end PI.UnitaryGroupMassFormula.UsCost
end
end

set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hd : ∀ i, d i ≠ 0) (η : XiH p s σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) :
    (ZjH σ d η Z).det ≠ 0 := by
  simp only [ZjH, Zj, blk2, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, headH, G.detM] at hZ ⊢
  simp only [lowW, G.upper]
  rw [det_one_add_strictLower _ (fun a b hab => ?_), det_one_add_strictUpper' _ (fun a b hab => ?_)]
  · rw [permutationMatrix_eq_permMatrix', Matrix.det_permutation, Matrix.det_diagonal]
    simp only [one_mul, mul_one]
    refine mul_ne_zero (mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)) hZ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · simp [G.strictUpper, not_lt.2 hab]
  · simp [not_lt.2 hab]
end PI.UnitaryGroupMassFormula.UsCost
