-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.IsFr.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:35.552987+00:00
-- url     : https://prove2.me/submissions/c285ad16-706d-427a-95d7-103c41b76928

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
namespace PositivityTheory.ThKCT.Fr
namespace IsFr
theorem _root_.solution (h : IsFr c ε J J₁ ι x y A') (hJ : IsUnit J.det) : IsUnit J₁.det := by
  have e1 : (fr ι x y).map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h.inv1, Matrix.map_one _ c.map_zero c.map_one]
  have e2 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have e3 : (fr ι x y)ᵀ * A'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h.inv2, Matrix.transpose_one]
  have hinv : gr ε J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1 := by
    rw [← h.gram]
    calc (fr ι x y)ᵀ * J * (fr ι x y).map c * (A'.map c * J⁻¹ * A'ᵀ)
        = (fr ι x y)ᵀ * (J * (((fr ι x y).map c * A'.map c) * J⁻¹)) * A'ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.one_mul, e2, Matrix.mul_one, e3]
  have hu : IsUnit (gr ε J₁).det := Matrix.isUnit_det_of_right_inverse hinv
  unfold gr at hu
  rw [Matrix.det_fromBlocks_zero₂₁] at hu
  exact isUnit_of_mul_isUnit_left hu
end IsFr
end PositivityTheory.ThKCT.Fr
