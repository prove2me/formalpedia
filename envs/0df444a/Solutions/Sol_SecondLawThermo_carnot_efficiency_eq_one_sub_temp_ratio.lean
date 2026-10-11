-- Prove2me | solution 1 for SecondLawThermo.carnot_efficiency_eq_one_sub_temp_ratio
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T04:02:01.947496+00:00
-- url     : https://prove2.me/submissions/751a47d5-9b49-4e59-8517-3d1d4527c2e5

import Definitions.Def_SecondLawThermo_Defs
import Theorems.Thm_SecondLawThermo_efficiency_eq_one_sub_abs_ratio
import Mathlib

open SecondLawThermo
local notation "Cycle" => SecondLawThermo.Cycle

theorem solution {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ))
    (T : Θ → ℝ)
    (hT : ∀ (h k : Θ) (e : Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = T k / T h)
    (h k : Θ) (hkh : k < h) (e : Cycle Θ) (he : IsCarnotEngine 𝒞 e h k) :
    efficiency e h = 1 - T k / T h := by
  rw [efficiency_eq_one_sub_abs_ratio e h k hkh.ne' he.2.1 he.2.2.1 he.2.2.2.1,
    hT h k e hkh he]
