-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.sw_zero1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:25.761266+00:00
-- url     : https://prove2.me/submissions/f120aae7-bbe8-428e-97d3-c2a2e21a641f

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_hcongr

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
theorem _root_.solution (y : B.G R) : B.sw (B.zero1 y) = B.zero2 y := by
  let a : B.S2 R y := ⟨0, B.sw (B.zero1 y)⟩
  have h : a + a = a := by
    refine Sigma.ext (add_zero (0 : B.G R)) ?_
    show HEq (B.add2 (B.sw (B.zero1 y)) (B.sw (B.zero1 y))) (B.sw (B.zero1 y))
    rw [← B.swap_addFst]
    exact B.sw_hcongr (add_zero 0) rfl (B.zeroFst_add _)
  exact eq_of_heq (Sigma.ext_iff.1 (B.fibreSnd_idem a h)).2
end ReciprocityTheory.PGsh.BX
