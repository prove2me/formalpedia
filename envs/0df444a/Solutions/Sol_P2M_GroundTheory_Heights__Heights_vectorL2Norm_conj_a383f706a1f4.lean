-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_vectorL2Norm_conj_a383f706a1f4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:59.185105+00:00
-- url     : https://prove2.me/submissions/5ce23cba-b4ab-4f71-8938-7bd4c66c341f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points

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
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (w : Fin m → ℂ) :
    l2Norm (fun i ↦ starRingEnd ℂ (w i)) = l2Norm w := by
  simp only [l2Norm, Complex.norm_conj]
end GroundTheory.Heights₂.Heights
