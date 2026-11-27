-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceRegTail_proof_05dd17c5c553
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:09:54.343801+00:00
-- url     : https://prove2.me/submissions/184f1095-c60f-4a15-8b5c-73d75d183b59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegVarBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceRegTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceRegTail_exists_bound_d01650779eca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_mem_Icc_57a0d0358e0c


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
open MvPolynomial Filter Topology Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace SliceRegTail
theorem _root_.solution (hB : SliceRegVarBound.Statement) (hT : SliceRegTailMass.Statement)
    (hM : SliceCutTailMass.Statement) : SliceRegTail.Statement := by
  intro n e h W F u' ℓ a hW hF hu hℓ hℓP ha hac δ hδ
  obtain ⟨C, hC0, hC⟩ := SliceRegTail.exists_bound ha hac
  have hδ' : 0 < δ / (3 * C) := by positivity
  obtain ⟨K₁, hK₁⟩ := hT n e h W F u' ℓ hW hF hu hℓ hℓP _ hδ'
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const hδ' (hM n e h W F ℓ hW hF hℓ))
  refine ⟨max K₁ K₂, fun k hk ε hε => ?_⟩
  have hma : Measurable a := measurable_of_continuousOn_compl_singleton 0 hac
  have hI := SliceCut.mem_Icc h k
  have hb := hB n e h W F u' ℓ ε C a (fun x => sliceCut h k x * a x) (fun x => 1 - sliceCut h k x)
    hW hF hℓ hε.1 hma ((SliceCut.measurable h k).mul hma) (measurable_const.sub (SliceCut.measurable h k)) hC
    (fun x => by
      rw [abs_mul, abs_of_nonneg (hI x).1]
      nlinarith [hC x, (hI x).1, (hI x).2, abs_nonneg (a x)])
    (fun x => ⟨by linarith [(hI x).2], by linarith [(hI x).1]⟩)
    (fun x => by
      rw [show a x - sliceCut h k x * a x = (1 - sliceCut h k x) * a x by ring, abs_mul,
        abs_of_nonneg (by linarith [(hI x).2] : (0 : ℝ) ≤ 1 - sliceCut h k x)]
      nlinarith [hC x, (hI x).1, (hI x).2, abs_nonneg (a x)])
  have h1 := hK₁ k (le_of_max_le_left hk) ε hε
  have h2 := hK₂ k (le_of_max_le_right hk)
  refine hb.trans ?_
  have h3 : C * (δ / (3 * C)) = δ / 3 := by field_simp
  nlinarith
end SliceRegTail
end GroundTheory.Heights₂.Heights
