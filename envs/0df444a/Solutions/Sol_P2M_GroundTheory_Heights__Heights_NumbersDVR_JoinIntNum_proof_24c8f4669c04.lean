-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_proof_24c8f4669c04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:30.673397+00:00
-- url     : https://prove2.me/submissions/c7bea257-278f-4fa8-b314-9b190823196f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_mixedDiff_map_ae37bf432065
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_EventualValueFacts_proof_11bc4474d04d


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
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution : JoinIntNum.Statement := by
  intro F _ K _ _ ι _ V n bs
  unfold intNum
  rw [funext (mixedDiff_map V bs)]
  set f := mixedDiff bs (hilbFn V)
  by_cases hc : ∃ c, ∀ᶠ m in Filter.atTop, f m = c
  · obtain ⟨c, hc⟩ := hc
    rw [(EventualValueFacts.proof K f c 0).1 hc]
    apply (EventualValueFacts.proof _ _ c 0).1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc
    refine Filter.eventually_atTop.mpr ⟨Sum.elim N 0, fun m' hm' => ?_⟩
    have ht : 0 ≤ m' (.inr ()) := by simpa using hm' (.inr ())
    rw [if_pos ht]
    exact hN _ (fun k => by simpa using hm' (.inl k))
  · have hc' : ¬ ∃ c, ∀ᶠ m' in Filter.atTop,
        (fun m' : K ⊕ Unit → ℤ => if 0 ≤ m' (.inr ()) then f (fun k => m' (.inl k)) else 0) m' =
          c := by
      rintro ⟨c, hc'⟩
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc'
      refine hc ⟨c, Filter.eventually_atTop.mpr ⟨fun k => N (.inl k), fun m hm => ?_⟩⟩
      have h := hN (Sum.elim m (fun _ => |N (.inr ())|)) ?_
      · simpa using h
      · rintro (k | u)
        · exact hm k
        · exact le_abs_self _
    rw [eventualValue, eventualValue, dif_neg hc, dif_neg hc']
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
