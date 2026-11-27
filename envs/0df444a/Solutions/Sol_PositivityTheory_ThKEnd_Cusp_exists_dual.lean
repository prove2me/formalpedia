-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:04.867196+00:00
-- url     : https://prove2.me/submissions/ec20c521-4d87-47b3-9d47-bb0827621775

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_map_map_c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open Matrix
variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}
namespace PositivityTheory.ThKEnd.Cusp
theorem _root_.solution {K : Type} [Field K] [CharZero K] {c : K →+* K} (cc : ∀ r, c (c r) = r) {J : Matrix n n K} (sk : (J.map c)ᵀ = -J)
    (hJ : J.det ≠ 0) {u : Matrix n ι K} (hu : Function.Injective u.mulVec) (uu : uᵀ * J * u.map c = 0) : ∃ u', Fr c J u u' := by
  obtain ⟨L, hL⟩ := u.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hu)
  have h1 : LinearMap.toMatrix' L * u = 1 := by
    rw [← LinearMap.toMatrix'_toLin' u, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hL, LinearMap.toMatrix'_id]
  set w := (J⁻¹ * (LinearMap.toMatrix' L)ᵀ).map c with hw
  have h2 : uᵀ * J * w.map c = 1 := by
    rw [hw, map_map_c cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.isUnit, ← transpose_mul, h1, transpose_one]
  have k : ∀ a b : Matrix n ι K, ((aᵀ * J * b.map c).map c)ᵀ = -(bᵀ * J * a.map c) := fun a b => by
    rw [Matrix.map_mul, Matrix.map_mul, map_map_c cc, transpose_mul, transpose_mul, sk, transpose_map, transpose_transpose]
    simp [Matrix.mul_assoc]
  have h3 : wᵀ * J * u.map c = -1 := by
    have := k u w
    rw [h2, Matrix.map_one _ (map_zero c) (map_one c), transpose_one] at this
    exact neg_eq_iff_eq_neg.1 this.symm
  set S := wᵀ * J * w.map c with hS
  have h4 : ((2 : K)⁻¹ • Sᵀ).map c = (2 : K)⁻¹ • -S := by
    rw [hS, ← k w w, ← hS]
    ext i j
    simp [map_ofNat]
  refine ⟨w - u * ((2 : K)⁻¹ • Sᵀ), cc, sk, uu, ?_, ?_⟩
  · rw [Matrix.map_sub _ (map_sub c), Matrix.map_mul, h4, transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, ← hS, ← Matrix.mul_assoc (wᵀ * J), h3, Matrix.mul_assoc _ uᵀ, Matrix.mul_assoc _ (uᵀ * J), h2,
      Matrix.mul_assoc _ (uᵀ * J), ← Matrix.mul_assoc (uᵀ * J), uu]
    ext i j
    simp
    ring
  · rw [Matrix.map_sub _ (map_sub c), Matrix.map_mul, Matrix.mul_sub, h2, ← Matrix.mul_assoc, uu, Matrix.zero_mul, sub_zero]
end PositivityTheory.ThKEnd.Cusp
