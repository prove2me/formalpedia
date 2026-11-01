-- Prove2me | solution 1 for WeakSignalBandit.marginal_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:39:10.192855+00:00
-- url     : https://prove2.me/submissions/300a0914-1289-4adc-8d3d-979359305b04

import Mathlib.Topology.Path
import Definitions.Def_WeakSignalBandit_DiffusionLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

open WeakSignalBandit

theorem solution {ι : Type*} [Fintype ι]
    (Pn : ℕ → Measure (Path ι)) [∀ n, IsProbabilityMeasure (Pn n)]
    (P : Measure (Path ι)) [IsProbabilityMeasure P]
    (hconv : ∀ F : Path ι →ᵇ ℝ, Tendsto (fun n => ∫ x, F x ∂(Pn n)) atTop (𝓝 (∫ x, F x ∂P)))
    (t : unitInterval) (f : Sp ι →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f (x t) ∂(Pn n)) atTop (𝓝 (∫ x, f (x t) ∂P)) := by
  have hEv : Continuous (fun x : Path ι => x t) :=
    Continuous.eval_const continuous_id t
  let ev : C(Path ι, Sp ι) := ⟨fun x => x t, hEv⟩
  have hh := hconv (f.compContinuous ev)
  simpa [ev] using hh
