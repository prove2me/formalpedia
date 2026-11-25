-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul1_zero2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:46:47.187183+00:00
-- url     : https://prove2.me/submissions/7d81afb1-b51a-4fad-85cf-e7b311725446

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_heq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (x : B.G R) (n : ℕ) : HEq (B.nsmul1 (B.zero2 x) n) (B.zero2 (n • x)) := by
  induction n with
  | zero =>
    refine (B.castFst_heq _ _).trans ?_
    rw [B.zeroFst_zero]; exact B.heq_zero2 (zero_nsmul x).symm
  | succ n ih =>
    refine (B.castFst_heq _ _).trans ?_
    refine (B.addFst_hcongr rfl rfl rfl ih HEq.rfl).trans ?_
    rw [zeroSnd_addFst]; exact B.heq_zero2 (succ_nsmul x n).symm
end ReciprocityTheory.PGsh.BX
