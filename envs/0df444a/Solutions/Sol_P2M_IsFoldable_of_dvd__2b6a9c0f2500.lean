-- Prove2me | solution 1 for P2M_IsFoldable_of_dvd__2b6a9c0f2500
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:02:44.27202+00:00
-- url     : https://prove2.me/submissions/e37ca14e-ac42-469e-afcc-9fcb8d7b834c

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
namespace IsFoldable
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] {D : Finset F} {m n : ℕ}
    (h : IsFoldable D m) (hd : n ∣ m) : IsFoldable D n :=
  let ⟨H, a, hD, hdiv⟩ := h; ⟨H, a, hD, hd.trans hdiv⟩
end IsFoldable
