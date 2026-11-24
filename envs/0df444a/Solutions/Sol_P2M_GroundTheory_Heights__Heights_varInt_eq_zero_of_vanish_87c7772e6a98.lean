-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:44.413874+00:00
-- url     : https://prove2.me/submissions/0f17379d-3298-4590-a821-ea43069595ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n k : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) (hf : ∀ x ∈ zeroSet W, f x = 0) :
    varInt W k f φ = 0 := by
  classical
  unfold varInt
  split_ifs with h
  · have h0 : chartDens W h.choose f φ = fun _ => 0 := by
      funext y
      unfold chartDens sheetSum
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      rw [finsum_eq_dif]
      by_cases hx : x ∈ fibre W h.choose y
      · rw [dif_pos hx]
        split_ifs
        · show f x * _ = 0
          rw [hf x hx.1, zero_mul]
        · rfl
      · rw [dif_neg hx]
    simp [chartInt, h0]
  · rfl
end GroundTheory.Heights₂.Heights
