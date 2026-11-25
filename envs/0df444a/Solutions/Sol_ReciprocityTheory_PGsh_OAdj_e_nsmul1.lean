-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.e_nsmul1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:07.28815+00:00
-- url     : https://prove2.me/submissions/05906908-2207-443e-b2e0-42301e976fb9

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_zero1
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
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)
namespace ReciprocityTheory.PGsh.OAdj
theorem _root_.solution (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ)
    (w : B.P R (A.a.f s (n • x)) z) (hw : HEq w (B.nsmul1 u n)) :
    HEq (A.e s (n • x) z w) (B.nsmul1 (A.e s x z u) n) := by
  induction n with
  | zero =>
    refine (A.e_hcongr s (zero_nsmul x) rfl
      (u₂ := B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z)) ?_).trans ?_
    · exact hw.trans ((B.castFst_heq _ _).trans (B.castFst_heq _ _).symm)
    · exact (A.e_zero1 s z).trans (B.castFst_heq _ _).symm
  | succ n ih =>
    have hn : A.a.f s (n • x) = n • A.a.f s x := map_nsmul _ n x
    have h1 := ih (B.tr1 hn.symm (B.nsmul1 u n)) (B.castFst_heq _ _)
    refine (A.e_hcongr s (succ_nsmul x n) rfl
      (u₂ := B.tr1 (map_add (A.a.f s) (n • x) x).symm (B.add1 (B.tr1 hn.symm (B.nsmul1 u n)) u))
      ?_).trans ?_
    · refine hw.trans ((B.castFst_heq _ _).trans ?_)
      exact (B.addFst_hcongr hn.symm rfl rfl (B.castFst_heq _ _).symm HEq.rfl).trans (B.castFst_heq _ _).symm
    · rw [A.equiv_addFst]
      exact (B.addFst_hcongr rfl rfl rfl h1 HEq.rfl).trans (B.castFst_heq _ _).symm
end ReciprocityTheory.PGsh.OAdj
