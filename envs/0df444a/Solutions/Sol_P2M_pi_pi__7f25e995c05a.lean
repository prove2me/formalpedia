-- Prove2me | solution 1 for P2M_pi_pi__7f25e995c05a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:37:52.200785+00:00
-- url     : https://prove2.me/submissions/e80aa16a-d390-4e49-821d-d890caa43112

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
open Classical
theorem _root_.solution {f : ι → Set Ω} {s : Finset ι} :
    (Measure.pi P) ((s : Set ι).pi f) = ∏ i ∈ s, P i (f i) := by
  have : (s : Set ι).pi f = Set.univ.pi (fun i ↦ if i ∈ s then f i else Set.univ) := by
    ext x
    simp
  simp [this, Measure.pi_pi, apply_ite]
