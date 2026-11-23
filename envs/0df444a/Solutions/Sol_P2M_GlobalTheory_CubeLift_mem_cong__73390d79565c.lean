-- Prove2me | solution 1 for P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:27.273472+00:00
-- url     : https://prove2.me/submissions/72b5d8b9-b2a8-4d56-8c61-58992eb99abb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_mem_cong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution {I : Ideal A} {u : (A[X])ˣ} : u ∈ cong I ↔ rd I (u.val - 1) = 0 := by
  rw [mem_cong, map_sub, map_one, sub_eq_zero]
end GlobalTheory.CubeLift
