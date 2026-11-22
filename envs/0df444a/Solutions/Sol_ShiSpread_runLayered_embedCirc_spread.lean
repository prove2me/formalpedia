-- Prove2me | solution 1 for ShiSpread.runLayered_embedCirc_spread
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-11T08:38:47.642928+00:00
-- url     : https://prove2.me/submissions/9f5b1232-e391-4bd3-b739-4a3d59271db5

import Theorems.Thm_ShiSpread_embedInstr_apply_spread

set_option autoImplicit false

section
open ShiSpread ShiEmbed ShiShallow

theorem solution {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (c : Layered m) (ψ : QState m) :
    runLayered (embedCirc e he c) (spread e ψ) = spread e (runLayered c ψ) := by
  have layer : ∀ (l : List (Instr m)) (χ : QState m),
      runLayer (embedLayer e he l) (spread e χ) = spread e (runLayer l χ) := by
    intro l
    induction l with
    | nil => intro χ; rfl
    | cons g t ih =>
      intro χ
      calc runLayer (embedLayer e he (g :: t)) (spread e χ)
          = runLayer (embedLayer e he t) (Instr.apply (embedInstr e he g) (spread e χ)) := rfl
        _ = runLayer (embedLayer e he t) (spread e (Instr.apply g χ)) := by
              rw [ShiSpread.embedInstr_apply_spread e he g χ]
        _ = spread e (runLayer t (Instr.apply g χ)) := ih (Instr.apply g χ)
        _ = spread e (runLayer (g :: t) χ) := rfl
  induction c generalizing ψ with
  | nil => rfl
  | cons l t ih =>
    calc runLayered (embedCirc e he (l :: t)) (spread e ψ)
        = runLayered (embedCirc e he t) (runLayer (embedLayer e he l) (spread e ψ)) := rfl
      _ = runLayered (embedCirc e he t) (spread e (runLayer l ψ)) := by rw [layer l ψ]
      _ = spread e (runLayered t (runLayer l ψ)) := ih (runLayer l ψ)
      _ = spread e (runLayered (l :: t) ψ) := rfl

end
