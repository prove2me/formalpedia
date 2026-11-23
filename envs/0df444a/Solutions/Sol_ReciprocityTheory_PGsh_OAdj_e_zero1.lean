-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.e_zero1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:33.289843+00:00
-- url     : https://prove2.me/submissions/5bb3d8d1-edf6-4578-96ff-03cdb4e9b34c

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_hcongr
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
theorem _root_.solution (z : B.G R) :
    HEq (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z))) (B.zero1 (A.ab.f s z)) := by
  set w0 := B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z) with hw0
  have hw : HEq w0 (B.zero1 z) := B.castFst_heq _ _
  have h1 := A.equiv_addFst s 0 0 z w0 w0
  have h2 : HEq (A.e s (0 + 0) z (B.tr1 (map_add (A.a.f s) 0 0).symm (B.add1 w0 w0)))
      (A.e s 0 z w0) := by
    refine A.e_hcongr s (add_zero 0) rfl ?_
    refine (B.castFst_heq _ _).trans ?_
    refine (B.addFst_hcongr (map_zero _) (map_zero _) rfl hw hw).trans ?_
    exact (B.zeroFst_add (B.zero1 z)).trans hw.symm
  have hid : B.S1mk (A.e s 0 z w0) + B.S1mk (A.e s 0 z w0) = B.S1mk (A.e s 0 z w0) :=
    Sigma.ext (add_zero (0 : B.G R)) ((heq_of_eq h1.symm).trans h2)
  exact (Sigma.ext_iff.1 (B.fibreFst_idem _ hid)).2
end ReciprocityTheory.PGsh.OAdj
