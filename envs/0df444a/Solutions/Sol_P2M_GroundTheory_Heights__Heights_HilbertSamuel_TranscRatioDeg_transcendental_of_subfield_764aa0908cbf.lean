-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_of_subfield_764aa0908cbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:02.169547+00:00
-- url     : https://prove2.me/submissions/c50e3c1b-d230-4734-9bb8-cc75e0c6f9c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LinearIndependentAdjoinOfTranscendental

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
open Polynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
theorem _root_.solution {E : Type*} [Field E] {S : Type*} [CommRing S] [Algebra S E]
    (Q : Subfield E) (h : ∀ x : S, algebraMap S E x ∈ Q) (hinj : Function.Injective (algebraMap S E))
    {t : E} (ht : Transcendental Q t) : Transcendental S t := by
  rintro ⟨p, hp0, hp⟩
  let φ : S →+* Q := (algebraMap S E).codRestrict Q h
  have hφ : Function.Injective φ := fun a b hab => hinj (congrArg Subtype.val hab :)
  refine ht ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ).2 hp0, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hp
end GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
