-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pmap_nsmul1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:44.427124+00:00
-- url     : https://prove2.me/submissions/0d824f83-240a-4d42-8fda-1db8313c8668

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk

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
    HEq (B.pmap f (B.nsmul1 u n)) (B.nsmul1 (B.pmap f u) n) := by
  have h := (B.PrimaryComponentMap f y).map_nsmul n (B.S1mk u)
  rw [fibreFst_nsmul_mk] at h
  have h' : (B.S1mk (B.pmap f (B.nsmul1 u n))) =
      n • (B.S1mk (B.pmap f u)) := h
  rw [fibreFst_nsmul_mk] at h'
  exact (Sigma.ext_iff.1 h').2
end ReciprocityTheory.PGsh.BX
