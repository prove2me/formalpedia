-- Prove2me | solution 1 for PassivityTorus.shift_back_forward
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T04:27:46.881774+00:00
-- url     : https://prove2.me/submissions/02bf2fcb-269a-413c-9edd-5dba193397c8

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorusSol
open PassivityTorus

theorem shift_apply_self {q L : ℕ} (x : Site q L) (a : Fin q) (s : Fin L) :
    shift x a s a = x a + s := by simp [shift]

theorem shift_apply_ne {q L : ℕ} (x : Site q L) {a b : Fin q} (s : Fin L) (h : b ≠ a) :
    shift x a s b = x b := by simp [shift, h]

end PassivityTorusSol

open PassivityTorus PassivityTorusSol

theorem solution {q L : ℕ} [NeZero L] (x : Site q L) (a : Fin q) :
    shift (shift x a (-1)) a 1 = x := by
  funext b
  by_cases h : b = a
  · subst h; simp [shift]
  · simp [shift, h]
