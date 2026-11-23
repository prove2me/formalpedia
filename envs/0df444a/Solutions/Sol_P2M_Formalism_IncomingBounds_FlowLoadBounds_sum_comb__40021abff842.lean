-- Prove2me | solution 1 for P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:48.298332+00:00
-- url     : https://prove2.me/submissions/462d1410-c611-441c-9439-7625f3446005

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, (a * f i + b * g i) = a * ∑ i ∈ S, f i + b * ∑ i ∈ S, g i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
end Formalism.IncomingBounds.FlowLoadBounds
