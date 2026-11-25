-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTEventuallyConst_proof_42eb709a2798
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:27.397187+00:00
-- url     : https://prove2.me/submissions/40644152-776c-4ab5-9fd1-ccd40e59023d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTEventuallyConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTEventuallyConst_eq_of_unitSteps_eq_zero_9eea2be60e1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.NumbersDVR.DegLTEventuallyConst
namespace GroundTheory.Heights₂.Heights.NumbersDVR.DegLTEventuallyConst
theorem _root_.solution (h1 : MixedDiffLinear.Statement) : DegLTEventuallyConst.Statement := by
  intro K _ _ n f hf bs
  have hev : ∀ k : K, ∀ᶠ m in Filter.atTop,
      mixedDiff bs f m - mixedDiff bs f (m - Pi.single k 1) = 0 := by
    intro k
    have hk := hf (Matrix.vecCons (Pi.single k 1) bs)
    rw [(h1 K n bs f 0 0 0 (Pi.single k 1)).2.2.2.2] at hk
    exact hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hev)
  exact ⟨mixedDiff bs f N, Filter.eventually_atTop.mpr ⟨N, fun m hm =>
    eq_of_unitSteps_eq_zero (mixedDiff bs f) N (fun m hm => hN m hm) _ m hm rfl⟩⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.DegLTEventuallyConst
