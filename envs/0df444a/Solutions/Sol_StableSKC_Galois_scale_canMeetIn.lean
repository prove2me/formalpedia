-- Prove2me | solution 1 for StableSKC.Galois.scale_canMeetIn
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:55:43.245649+00:00
-- url     : https://prove2.me/submissions/0de68b3c-6649-49e6-a556-cbc291f85457

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

set_option autoImplicit false

open StableSKC.Galois

theorem solution {k : ℕ} {F : Type*} [Field F] (T : Seeding k F) (z : Fˣ) (x y : F)
    (i : ℕ) :
    CanMeetIn (scale T z) x y i ↔ CanMeetIn T ((↑z⁻¹ : F) * x) ((↑z⁻¹ : F) * y) i := by
  rfl
