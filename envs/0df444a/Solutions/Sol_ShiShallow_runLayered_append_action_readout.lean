-- Prove2me | solution 1 for ShiShallow.runLayered_append_action_readout
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T07:22:19.956836+00:00
-- url     : https://prove2.me/submissions/ba077617-3f13-469b-9474-41877834044f

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

/-- Splitting a layered circuit at an append: the first block runs first. -/
private lemma shiGlu_runLayered_append {N : ℕ} (c₁ c₂ : Layered N) (φ : QState N) :
    runLayered (c₁ ++ c₂) φ = runLayered c₂ (runLayered c₁ φ) := by
  first
    | (unfold runLayered; rw [List.foldl_append]; done)
    | (simp only [runLayered, List.foldl_append]; done)
    | (simp [runLayered]; done)

theorem solution {N : ℕ} (cA cR : Layered N)
    (fA : QState N → QState N) (uR : Bits N → Bits N)
    (hA : ∀ ψ, runLayered cA ψ = fA ψ)
    (hR : ∀ ψ, runLayered cR ψ = fun x => ψ (uR x))
    (ψ : QState N) :
    runLayered (cA ++ cR) ψ = fun x => fA ψ (uR x) :=
  calc runLayered (cA ++ cR) ψ
      = runLayered cR (runLayered cA ψ) := shiGlu_runLayered_append cA cR ψ
    _ = runLayered cR (fA ψ) := by
        first
          | (exact congrArg (runLayered cR) (hA ψ))
          | (rw [hA ψ]; done)
          | (rw [hA]; done)
    _ = fun x => fA ψ (uR x) := hR (fA ψ)
