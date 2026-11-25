-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_mem_nonZeroDivisors_of_notMem_minimalPrimes_4676f1a7448f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:24.08602+00:00
-- url     : https://prove2.me/submissions/ddaa7104-b8c7-43a7-90f6-5ef6f1702dc4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac

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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.MinimalPrimePlace
theorem _root_.solution [IsReduced A] {w : A}
    (hw : ∀ q ∈ minimalPrimes A, w ∉ q) : w ∈ nonZeroDivisors A := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩ <;>
    refine eq_zero_of_forall_mem_minimalPrimes fun q hq ↦ ?_
  · exact (hq.1.1.mem_or_mem (hy ▸ q.zero_mem : w * y ∈ q)).resolve_left (hw q hq)
  · exact (hq.1.1.mem_or_mem (hy ▸ q.zero_mem : y * w ∈ q)).resolve_right (hw q hq)
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
