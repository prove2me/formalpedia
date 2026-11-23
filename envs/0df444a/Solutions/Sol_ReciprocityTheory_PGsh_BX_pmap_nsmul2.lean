-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pmap_nsmul2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:05.522889+00:00
-- url     : https://prove2.me/submissions/6e6bb5ba-0761-4160-a3f5-9d214e4f55a7

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_mk

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
theorem _root_.solution {S : LAlg R₀} (f : LHom R S) {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    HEq (B.pmap f (B.nsmul2 u n)) (B.nsmul2 (B.pmap f u) n) := by
  have h := (B.SecondaryComponentMap f x).map_nsmul n (B.S2mk u)
  rw [fibreSnd_nsmul_mk] at h
  have h' : (B.S2mk (B.pmap f (B.nsmul2 u n))) =
      n • (B.S2mk (B.pmap f u)) := h
  rw [fibreSnd_nsmul_mk] at h'
  exact (Sigma.ext_iff.1 h').2
end ReciprocityTheory.PGsh.BX
