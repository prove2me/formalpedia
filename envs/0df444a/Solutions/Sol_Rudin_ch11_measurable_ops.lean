-- Prove2me | solution 1 for Rudin.ch11_measurable_ops
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:35.173444+00:00
-- url     : https://prove2.me/submissions/821adbee-fd67-46ce-8b72-c7350e735352

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorems 11.16 and 11.18: if `f` and `g` are measurable then so are `|f|`, `f + g`
and `f g`. -/
theorem solution {X : Type*} [MeasurableSpace X] (f g : X → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => |f x|) ∧ Measurable (fun x => f x + g x) ∧
      Measurable (fun x => f x * g x) := by
  exact ⟨hf.abs, hf.add hg, hf.mul hg⟩

#print axioms solution
