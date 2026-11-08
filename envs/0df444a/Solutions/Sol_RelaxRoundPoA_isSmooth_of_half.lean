-- Prove2me | solution 1 for RelaxRoundPoA.isSmooth_of_half
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:20:55.013181+00:00
-- url     : https://prove2.me/submissions/d7a3c19a-ebe1-49fe-8960-e6c465eb1c1a

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_IsSmooth
import Definitions.Def_RelaxRoundPoA_IsSmoothHalf

open MeasureTheory NNReal

open RelaxRoundPoA in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (lam mu : ℝ) (hhalf : HalfClosed Val)
    (h : IsSmoothHalf Val Feas M lam mu) :
    IsSmooth Val Feas M lam mu := by
  obtain ⟨hl, hm, hH⟩ := h
  refine ⟨hl, hm, fun v hv => ?_⟩
  refine ⟨fun i _ =>
    { A := PUnit
      P := Measure.dirac PUnit.unit
      X := fun _ y => v i y / 2
      mem := fun _ => hhalf i (v i) (hv i) }, fun b hb => ⟨fun i => by dsimp only; exact integrable_const _, ?_⟩⟩
  intro x hx
  refine le_trans (hH v hv b hb x hx) (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro i _
  simp
