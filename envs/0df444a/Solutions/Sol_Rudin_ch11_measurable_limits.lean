-- Prove2me | solution 1 for Rudin.ch11_measurable_limits
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:35.815259+00:00
-- url     : https://prove2.me/submissions/fd1ea113-e6fb-4909-add5-e52c5a4670c3

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorem 11.17: the pointwise supremum and the upper limit of a sequence of measurable
functions are measurable.  As in Rudin the functions take values in the extended half-line, so
that the supremum and the upper limit are always defined. -/
theorem solution {X : Type*} [MeasurableSpace X] (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => ⨆ n, f n x) ∧
      Measurable (fun x => limsup (fun n => f n x) atTop) := by
  exact ⟨Measurable.iSup hf, Measurable.limsup hf⟩

#print axioms solution
