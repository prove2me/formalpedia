-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.hTens_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:35.317665+00:00
-- url     : https://prove2.me/submissions/b2054d11-c220-4489-8077-b3a191422ce3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_hTens_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α'] [DecidableEq α']
  [Fintype β'] [DecidableEq β']
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution (JA : Matrix α α E) (JB : Matrix β β E) (a : Matrix α α' E) (b : Matrix β β' E) (x y : Matrix α' β' E) :
    hTens c JA JB (a * x * bᵀ) (a * y * bᵀ) = hTens c (aᵀ * JA * a.map c) (bᵀ * JB * b.map c) x y := by
  rw [hTens_eq, hTens_eq]
  have hm : (a * y * bᵀ).map c = a.map c * y.map c * (b.map c)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  rw [hm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm b]
  simp only [Matrix.mul_assoc]
end PositivityTheory.ThKF0.Geo
