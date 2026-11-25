-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.pairing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:22.483016+00:00
-- url     : https://prove2.me/submissions/43763436-bbcf-4b61-a042-6378af9ac09d

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_pairing_of
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)
namespace ReciprocityTheory.PGsh.OAdj
theorem _root_.solution (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0) (hz : N • z = 0) :
    B.IsPairing N (A.a.f s x) z w ↔ B.IsPairing N x (A.ab.f s z) w := by
  refine ⟨A.pairing_of s N x z w hx, fun h => ?_⟩
  have hax : N • A.a.f s x = 0 := by rw [← map_nsmul, hx, map_zero]
  obtain ⟨w', hw'⟩ := B.pairing_exists N _ z hax hz
  rwa [B.pairing_unique N x _ _ _ (A.pairing_of s N x z w' hx hw') h] at hw'
end ReciprocityTheory.PGsh.OAdj
