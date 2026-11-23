-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.e_zero2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:32.036982+00:00
-- url     : https://prove2.me/submissions/1c44bf71-5285-4a29-b828-8b70bae11234

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_hcongr

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
theorem _root_.solution (x : B.G R) : HEq (A.e s x 0 (B.zero2 (A.a.f s x))) (B.zero2 x) := by
  set w0 := B.zero2 (A.a.f s x) with hw0
  have h1 := A.equiv_addSnd s x 0 0 w0 w0
  have h2 : HEq (A.e s x (0 + 0) (B.add2 w0 w0)) (A.e s x 0 w0) :=
    A.e_hcongr s rfl (add_zero 0) (B.zeroSnd_add w0)
  have hz : A.ab.f s 0 + A.ab.f s 0 = A.ab.f s 0 := by rw [map_zero, add_zero]
  have hid : B.S2mk (A.e s x 0 w0) + B.S2mk (A.e s x 0 w0) = B.S2mk (A.e s x 0 w0) :=
    Sigma.ext hz ((B.castSnd_heq _ _).symm.trans ((heq_of_eq h1).symm.trans h2))
  exact (Sigma.ext_iff.1 (B.fibreSnd_idem _ hid)).2
end ReciprocityTheory.PGsh.OAdj
