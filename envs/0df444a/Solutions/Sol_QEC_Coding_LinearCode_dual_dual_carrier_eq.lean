-- Prove2me | solution 1 for QEC.Coding.LinearCode.dual_dual_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:39.487346+00:00
-- url     : https://prove2.me/submissions/1bf767d2-2399-4aea-9069-87a40013325c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι) : C.dual.dual.carrier = C.carrier := by
  let pairing := LinearMap.BilinForm.flipHom (wordPairing (F := F) (ι := ι))
  have hNondegenerate : pairing.Nondegenerate :=
    (wordPairing_nondegenerate (F := F) (ι := ι)).flip
  have hRefl : pairing.IsRefl := by
    intro x y hxy
    change wordPairing y x = 0 at hxy
    change wordPairing x y = 0
    rw [wordPairing_apply, dotProduct_comm]
    exact hxy
  change pairing.orthogonal (pairing.orthogonal C.carrier) = C.carrier
  exact pairing.orthogonal_orthogonal hNondegenerate hRefl C.carrier
end QEC.Coding.LinearCode
