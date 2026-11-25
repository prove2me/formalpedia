-- Prove2me | solution 1 for P2M_GlobalTheory_eval_Hom_detProdPoly_9518250e38f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:36.106481+00:00
-- url     : https://prove2.me/submissions/d4f39c94-adb1-4c61-81f5-0034afe4d44c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]
namespace GlobalTheory
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] {n : ι → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)] (f : R →+* S) (ξ : EntryIndex n n → S) :
    MvPolynomial.eval₂Hom f ξ (detProdPoly R n) = ∏ s, (ofEntries ξ s).det := by
  rw [detProdPoly, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp
end GlobalTheory
