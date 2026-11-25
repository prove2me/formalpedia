-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_aeval_mem_affPiece_0c0745e4a5a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:25.638262+00:00
-- url     : https://prove2.me/submissions/16f8efcd-2bf6-4cfb-babd-694609203a5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hj : y j ≠ 0) (f : Poly k N) :
    aeval (aff y j) f ∈ affPiece k y j f.totalDegree := by
  rw [show aeval (aff y j) f = ∑ d ∈ Finset.range (f.totalDegree + 1),
      aeval (aff y j) (homogeneousComponent d f) by rw [← map_sum, sum_homogeneousComponent]]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hd' : d ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  exact affPiece_mono hj hd' (Submodule.subset_span ⟨_, homogeneousComponent_isHomogeneous d f, rfl⟩)
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
