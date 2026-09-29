-- Prove2me | solution 1 for Rudin.ch11_integral_countably_additive
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:36.38631+00:00
-- url     : https://prove2.me/submissions/fca2c56c-cbdc-44c9-be3a-4ffe9daedb6b

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
/-- Rudin, Theorem 11.24: the integral of an integrable function is a countably additive set
function. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Function.onFun Disjoint E)) :
    HasSum (fun n => ∫ x in E n, f x ∂μ) (∫ x in ⋃ n, E n, f x ∂μ) := by
  exact hasSum_integral_iUnion hE hdisj hf.integrableOn

#print axioms solution
