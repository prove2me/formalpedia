-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointIntegral_zeroSet_ker_eval_4be2b8aa0b5c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:45.639144+00:00
-- url     : https://prove2.me/submissions/9e61b1b9-0314-4202-8e87-de9a667b7d28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.PointIntegral
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointIntegral
theorem _root_.solution (p : Fin n → ℂ) :
    zeroSet (RingHom.ker (MvPolynomial.eval p)) = {p} := by
  ext x
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, RingHom.mem_ker]
  constructor
  · intro h
    funext i
    have := h (X i - C (p i)) (by simp)
    simpa [sub_eq_zero] using this
  · rintro rfl q hq
    exact hq
end GroundTheory.Heights₂.Heights.PointIntegral
