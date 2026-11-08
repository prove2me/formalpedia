-- Prove2me | solution 1 for ProphetMatchingEFGT.xopt_mem_FM
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:52:01.526204+00:00
-- url     : https://prove2.me/submissions/a4ae6531-531d-434f-a354-1c21f794e9db

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_BatchedModel
import Definitions.Def_ProphetMatchingEFGT_MatchingModel

open MeasureTheory

open ProphetMatchingEFGT in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : Edge G → Measure ℝ) [∀ e, IsProbabilityMeasure (F e)]
    (opt : (Edge G → ℝ) → Finset (Edge G)) (hopt : IsOPT (matchingFamily G) opt) :
    InFM G (fun e => (Measure.pi F).real {w | e ∈ opt w}) := by
  have hmeas : ∀ e, MeasurableSet {w : Edge G → ℝ | e ∈ opt w} := by
    intro e
    have : {w : Edge G → ℝ | e ∈ opt w} = ⋃ (S : Finset (Edge G)) (_ : e ∈ S), {w | opt w = S} := by
      ext w
      simp
    rw [this]
    exact MeasurableSet.iUnion fun S => MeasurableSet.iUnion fun _ => hopt.measurableSet_eq S
  refine ⟨fun e => measureReal_nonneg, fun v => ?_⟩
  refine le_trans (le_of_eq (measureReal_biUnion_finset
    (f := fun e => {w : Edge G → ℝ | e ∈ opt w}) ?_ ?_ (fun b _ => measure_ne_top _ _)).symm)
    measureReal_le_one
  · intro e he f hf hef
    refine Set.disjoint_left.mpr (fun w hwe hwf => ?_)
    have hve : v ∈ (e : Sym2 V) := (Finset.mem_filter.mp he).2
    have hvf : v ∈ (f : Sym2 V) := (Finset.mem_filter.mp hf).2
    exact (hopt.mem w) e hwe f hwf hef v hve hvf
  · intro e _
    exact hmeas e
