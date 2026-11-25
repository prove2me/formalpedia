-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.e_nsmul2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:09.373125+00:00
-- url     : https://prove2.me/submissions/dd4bdcd4-d242-4071-8294-12f6abc4b2aa

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_zero2

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
theorem _root_.solution (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ) :
    HEq (A.e s x (n • z) (B.nsmul2 u n)) (B.nsmul2 (A.e s x z u) n) := by
  induction n with
  | zero =>
    exact (A.e_hcongr s rfl (zero_nsmul z) (B.castSnd_heq _ _)).trans
      ((A.e_zero2 s x).trans (B.castSnd_heq _ _).symm)
  | succ n ih =>
    refine (A.e_hcongr s rfl (succ_nsmul z n) (B.castSnd_heq _ _)).trans ?_
    rw [A.equiv_addSnd]
    refine (B.castSnd_heq _ _).trans ?_
    exact (B.addSnd_hcongr rfl (map_nsmul _ n z) rfl ih HEq.rfl).trans (B.castSnd_heq _ _).symm
end ReciprocityTheory.PGsh.OAdj
