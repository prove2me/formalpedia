-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mulVec_cons_of_row_zero_5b804bab8996
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:36.40229+00:00
-- url     : https://prove2.me/submissions/f45bcbdf-bb7d-487b-a62f-1dbecf99ef74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
theorem _root_.solution (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (y : Fin e → ℂ) :
    T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) =
      Fin.cons (T 0 0) ((fun i => T i.succ 0) + (T.submatrix Fin.succ Fin.succ) *ᵥ y) := by
  funext p
  refine Fin.cases ?_ (fun i => ?_) p
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, hT]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ]
end GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
