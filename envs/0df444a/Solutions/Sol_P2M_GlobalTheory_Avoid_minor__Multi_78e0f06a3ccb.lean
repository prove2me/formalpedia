-- Prove2me | solution 1 for P2M_GlobalTheory_Avoid_minor__Multi_78e0f06a3ccb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:42.341465+00:00
-- url     : https://prove2.me/submissions/a5cbdc25-78c8-4d7c-b003-133d1dcd6027

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower
namespace GlobalTheory.Avoid
theorem _root_.solution {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [LinearOrder ι]
    (c : ι → Dual R V) {r : ℕ} (J : Set.powersetCard ι r) (v : Fin r → V) :
    pairingDual R V r (ιMulti_family R r c J) (ιMulti R r v) =
      (Matrix.of fun i j => c (Set.powersetCard.ofFinEmbEquiv.symm J j) (v i)).det := by
  simp [ιMulti_family, pairingDual_ιMulti_ιMulti]
end GlobalTheory.Avoid
