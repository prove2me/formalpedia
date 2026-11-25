-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_isIntegral_of_forall_place_lt_one_7a41888a79e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:24.526317+00:00
-- url     : https://prove2.me/submissions/1ab81d9d-5c18-47d0-88cd-c8650df91996

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {c : K}
    (hc : IsIntegral ℤ c) (hlt : ∀ w : InfinitePlace K, w c < 1) : c = 0 := by
  by_contra hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have ha : (⟨c, hc⟩ : 𝓞 K) ≠ 0 := fun h0 => hne (congrArg ((↑) : 𝓞 K → K) h0)
  exact absurd (InfinitePlace.one_le_of_lt_one ha (fun z _ => hlt z)) (not_le.2 (hlt w))
end GroundTheory.Heights₂.Heights.FiniteCovolume
