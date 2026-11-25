-- Prove2me | solution 1 for ReciprocityTheory.PGsh.OAdj.pairing_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:10.065821+00:00
-- url     : https://prove2.me/submissions/d454c33a-c68a-45fc-9de7-4896e31732a0

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_zero1
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_zero2
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_nsmul1
import Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_nsmul2
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_heq
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_smul_hcongr


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
theorem _root_.solution (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0)
    (h : B.IsPairing N (A.a.f s x) z w) : B.IsPairing N x (A.ab.f s z) w := by
  obtain ⟨hax, hz, u, l₁, l₂, h1, h2, rfl⟩ := h
  have hbz : N • A.ab.f s z = 0 := by rw [← map_nsmul, hz, map_zero]
  refine ⟨hx, hbz, A.e s x z u, l₁, l₂, ?_, ?_, rfl⟩
  · have hn : A.a.f s (N • x) = N • A.a.f s x := map_nsmul _ N x
    have k1 := A.e_nsmul1 s x z u N (B.tr1 hn.symm (B.nsmul1 u N)) (B.castFst_heq _ _)
    have k2 : HEq (A.e s (N • x) z (B.tr1 hn.symm (B.nsmul1 u N)))
        (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.smul l₁ (B.zero1 z)))) := by
      refine A.e_hcongr s hx rfl ?_
      refine (B.castFst_heq _ _).trans ?_
      exact ((B.castFst_heq hax _).symm.trans (heq_of_eq h1)).trans (B.castFst_heq _ _).symm
    rw [B.castFst_smul, A.e_smul] at k2
    apply eq_of_heq
    refine (B.castFst_heq _ _).trans (k1.symm.trans (k2.trans ?_))
    exact B.smul_hcongr rfl rfl l₁ (A.e_zero1 s z)
  · have k1 := A.e_nsmul2 s x z u N
    have k2 : HEq (A.e s x (N • z) (B.nsmul2 u N))
        (A.e s x 0 (B.smul l₂ (B.zero2 (A.a.f s x)))) :=
      A.e_hcongr s rfl hz ((B.castSnd_heq hz _).symm.trans (heq_of_eq h2))
    rw [A.e_smul] at k2
    apply eq_of_heq
    refine (B.castSnd_heq _ _).trans (k1.symm.trans (k2.trans ?_))
    exact B.smul_hcongr rfl (map_zero _) l₂ (A.e_zero2 s x)
end ReciprocityTheory.PGsh.OAdj
