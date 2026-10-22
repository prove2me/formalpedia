-- Prove2me | solution 1 for OpenPitMIP.UltPit.x1_feasible_upit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:03:50.713864+00:00
-- url     : https://prove2.me/submissions/4eeacc9c-17e9-4cbe-88c2-c3c49dbfc437

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

set_option autoImplicit false
open OpenPitMIP.UltPit PCPSPC

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    I.UPitFeasible (fun c => ∑ t, x c t) := by
  obtain ⟨hx, hle, harc, -, hy, -⟩ := hxy
  have hnn : ∀ c t, 0 ≤ x c t := by
    intro c t
    obtain ⟨b, rfl⟩ := hI.clu_surjective c
    rw [hx]
    exact Finset.sum_nonneg (fun d _ => hy b d t)
  refine ⟨?_, ?_⟩
  · intro c c' hc
    show ∑ t, x c t ≤ ∑ t, x c' t
    cases T with
    | zero => simp
    | succ n =>
      have h := harc c c' hc (Fin.last n)
      have e : Finset.Iic (Fin.last n) = (Finset.univ : Finset (Fin (n+1))) := by
        ext i; simp [Fin.le_last]
      simpa [cum, e] using h
  · intro c
    exact ⟨Finset.sum_nonneg (fun t _ => hnn c t), hle c⟩
