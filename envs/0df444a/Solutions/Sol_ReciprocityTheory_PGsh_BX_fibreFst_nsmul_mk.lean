-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.fibreFst_nsmul_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:51.765986+00:00
-- url     : https://prove2.me/submissions/7f65dbdf-88d8-4533-b4a5-a402fb858809

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
theorem _root_.solution {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    (n • (B.S1mk u)) = ⟨n • x, B.nsmul1 u n⟩ := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    exact Sigma.ext (zero_nsmul x).symm (B.castFst_heq (zero_nsmul x).symm (B.zero1 y)).symm
  | succ n ih =>
    rw [succ_nsmul, ih]
    exact Sigma.ext (succ_nsmul x n).symm (B.castFst_heq (succ_nsmul x n).symm _).symm
end ReciprocityTheory.PGsh.BX
