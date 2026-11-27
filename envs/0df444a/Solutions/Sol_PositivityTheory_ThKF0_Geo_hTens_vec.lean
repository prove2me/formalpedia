-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.hTens_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:41.59286+00:00
-- url     : https://prove2.me/submissions/0b90ce9f-bf11-4851-9a4e-756a3cad3f00

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg

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
theorem _root_.solution (JA : Matrix α α E) (JB : Matrix β β E) (w : Matrix α β E) (a : α → E) (b : β → E) :
    hTens c JA JB w (vecMulVec a b) = (JA *ᵥ fun i => c (a i)) ⬝ᵥ (w *ᵥ (JB *ᵥ fun i => c (b i))) := by
  simp only [hTens, vecMulVec_apply, map_mul, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring
end PositivityTheory.ThKF0.Geo
