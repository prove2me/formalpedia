-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.IsFr.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:12.053169+00:00
-- url     : https://prove2.me/submissions/9d7bd5bc-250d-4067-9f5e-2668496d36fe

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
namespace PositivityTheory.ThKG.Tow.Levi
namespace IsFr
theorem _root_.solution (h : IsFr c J J₁ ι x y) (hJ : IsUnit J.det) : IsUnit J₁.det := by
  obtain ⟨hg, A', h1, h2⟩ := h
  have e1 : (fr ι x y).map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : gr J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1 := by
    rw [← hg]
    calc _ = (fr ι x y)ᵀ * (J * ((fr ι x y).map c * A'.map c) * J⁻¹) * A'ᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, mul_nonsing_inv _ hJ, Matrix.mul_one, ← transpose_mul, h2, transpose_one]
  have e3 := Matrix.isUnit_det_of_right_inverse e2
  rw [gr, det_fromBlocks_zero₂₁] at e3
  exact isUnit_of_mul_isUnit_left e3
end IsFr
end PositivityTheory.ThKG.Tow.Levi
