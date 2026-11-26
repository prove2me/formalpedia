-- Prove2me | solution 1 for capAux_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:17.960175+00:00
-- url     : https://prove2.me/submissions/e0727c02-1ca1-41b4-b09c-2cb5b98ab159

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    ∀ n i, i < n → (capAux π m hsup h0 n).val i = capBound π m hsup h0 i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hval : (capAux π m hsup h0 (n + 1)).val
        = Function.update (capAux π m hsup h0 n).val n
            (cap_exists_ext π m hsup (capAux π m hsup h0 n).2).choose := rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [hval, Function.update_of_ne (by omega)]
      exact ih i h
    · subst h
      simp only [capBound]
