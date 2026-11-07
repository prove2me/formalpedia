-- Prove2me | solution 2 for Real.analyticAt_sinc
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:59:10.374198+00:00
-- url     : https://prove2.me/submissions/c26687ea-0e6d-403d-ab0c-8865b1435769

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Effectiveness
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
theorem solution (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rw [Real.sinc_eq_dslope]
  by_cases same : x = 0
  · subst x
    obtain ⟨series, analytic⟩ := (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0)
    exact ⟨series.fslope, analytic.has_fpower_series_dslope_fslope⟩
  · have analytic : AnalyticAt ℝ (fun y : ℝ => (Real.sin y - Real.sin 0) / (y - 0)) x :=
      (Real.analyticAt_sin.sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr same)
    apply analytic.congr
    filter_upwards [isOpen_ne.mem_nhds same] with y other
    simp only [dslope_of_ne Real.sin other, slope_def_field]
