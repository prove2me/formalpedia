-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmulFst_addSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:33:13.089793+00:00
-- url     : https://prove2.me/submissions/dcb78580-221d-4ccd-a41a-ef62b49e65b0

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
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
theorem _root_.solution {x y y' : B.G R} (u : B.P R x y) (u' : B.P R x y') (n : ℕ) :
    B.nsmul1 (B.add2 u u') n = B.add2 (B.nsmul1 u n) (B.nsmul1 u' n) := by
  induction n with
  | zero =>
    apply eq_of_heq
    show HEq (B.tr1 _ (B.zero1 (y + y')))
      (B.add2 (B.tr1 _ (B.zero1 y)) (B.tr1 _ (B.zero1 y')))
    refine (B.castFst_heq _ _).trans ?_
    refine (heq_of_eq (B.zeroFst_addSnd y y')).symm.trans ?_
    exact B.addSnd_hcongr (zero_nsmul x).symm rfl rfl
      (B.castFst_heq _ _).symm (B.castFst_heq _ _).symm
  | succ n ih =>
    apply eq_of_heq
    show HEq (B.tr1 _ (B.add1 (B.nsmul1 (B.add2 u u') n) (B.add2 u u')))
      (B.add2 (B.tr1 _ (B.add1 (B.nsmul1 u n) u))
        (B.tr1 _ (B.add1 (B.nsmul1 u' n) u')))
    refine (B.castFst_heq _ _).trans ?_
    rw [ih, ← B.interchange]
    exact B.addSnd_hcongr (succ_nsmul x n).symm rfl rfl
      (B.castFst_heq _ _).symm (B.castFst_heq _ _).symm
end ReciprocityTheory.PGsh.BX
