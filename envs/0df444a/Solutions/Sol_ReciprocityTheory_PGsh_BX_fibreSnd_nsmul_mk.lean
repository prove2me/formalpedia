-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.fibreSnd_nsmul_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:59.939343+00:00
-- url     : https://prove2.me/submissions/69253bbb-8c81-4905-a403-722be08a86c0

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst

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
    (n • (B.S2mk u)) = ⟨n • y, B.nsmul2 u n⟩ := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    exact Sigma.ext (zero_nsmul y).symm (B.castSnd_heq (zero_nsmul y).symm (B.zero2 x)).symm
  | succ n ih =>
    rw [succ_nsmul, ih]
    exact Sigma.ext (succ_nsmul y n).symm (B.castSnd_heq (succ_nsmul y n).symm _).symm
end ReciprocityTheory.PGsh.BX
