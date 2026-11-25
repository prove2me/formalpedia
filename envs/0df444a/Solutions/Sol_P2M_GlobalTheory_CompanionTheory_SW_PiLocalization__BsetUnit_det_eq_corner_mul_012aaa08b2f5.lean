-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_det_eq_corner_mul_012aaa08b2f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:17.114981+00:00
-- url     : https://prove2.me/submissions/40d684a4-921e-4c0f-a481-699537da157a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
theorem _root_.solution {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : K) (hw : S 0 0 * w = 1) :
    S.det = S 0 0 *
      (Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ).det := by
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
    { toFun := Sum.elim (fun _ => 0) Fin.succ
      invFun := fun i => Fin.cases (Sum.inl ()) Sum.inr i
      left_inv := by rintro (_ | j) <;> simp
      right_inv := by intro i; refine Fin.cases ?_ ?_ i <;> simp }
  have h1 : S.det = (S.submatrix e e).det := (Matrix.det_submatrix_equiv_self e S).symm
  let A : Matrix Unit Unit K := fun _ _ => S 0 0
  let B : Matrix Unit (Fin n) K := fun _ j => S 0 j.succ
  let C : Matrix (Fin n) Unit K := fun i _ => S i.succ 0
  let D : Matrix (Fin n) (Fin n) K := fun i j => S i.succ j.succ
  let Wm : Matrix Unit Unit K := fun _ _ => w
  have h2 : S.submatrix e e = Matrix.fromBlocks A B C D := by
    ext (_ | i) (_ | j) <;> rfl
  letI : Invertible A :=
    ⟨Wm, by ext i j; rw [Matrix.mul_apply]; simp [A, Wm]; rw [mul_comm]; exact hw,
      by ext i j; rw [Matrix.mul_apply]; simp [A, Wm, hw]⟩
  have hA : A.det = S 0 0 := by rw [Matrix.det_unique]
  have hD : D - C * ⅟A * B =
      Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ := by
    have hinv : ⅟A = Wm := rfl
    ext i j
    rw [hinv, Matrix.sub_apply, Matrix.mul_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply, Matrix.of_apply]
    simp [C, B, D, Wm]
  rw [h1, h2, Matrix.det_fromBlocks₁₁, hA, hD]
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
