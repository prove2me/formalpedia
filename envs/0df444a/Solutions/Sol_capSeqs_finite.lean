-- Prove2me | solution 1 for capSeqs_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:03.342408+00:00
-- url     : https://prove2.me/submissions/0e81a882-4235-4a60-82b4-b551e5532190

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
theorem _root_.solution (β : ℕ → ℕ) (n : ℕ) : (capSeqs β n).Finite := by
  have hsub : capSeqs β n ⊆
      (fun g : Fin n → ℕ => fun i => if h : i < n then g ⟨i, h⟩ else 0) ''
        (Set.pi univ fun j : Fin n => Iic (β j)) := by
    rintro s ⟨h1, h2⟩
    refine ⟨fun j => s j, ?_, ?_⟩
    · intro j _; exact h1 j j.isLt
    · funext i
      by_cases h : i < n
      · simp [h]
      · simp [h, h2 i (by omega)]
  have hfin : (Set.pi univ fun j : Fin n => Iic (β (j : ℕ))).Finite :=
    Set.Finite.pi fun j => Set.finite_Iic (β (j : ℕ))
  exact (hfin.image _).subset hsub
