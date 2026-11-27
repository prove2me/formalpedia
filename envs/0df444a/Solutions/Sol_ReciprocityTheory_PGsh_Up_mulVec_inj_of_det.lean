-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mulVec_inj_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:37.885108+00:00
-- url     : https://prove2.me/submissions/db55c3be-b8c6-4cb0-b7cb-b21599cd4d8d

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (hA : A.det ≠ 0) {x y : Fin s → R}
    (h : A *ᵥ x = A *ᵥ y) : x = y := by
  by_contra hne
  apply hA
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  rw [Matrix.mulVec_sub, h, sub_self]
end ReciprocityTheory.PGsh.Up
