-- Prove2me | solution 1 for ProbabilityTheory.Copula.measurePreserving_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:56.101121+00:00
-- url     : https://prove2.me/submissions/11021aef-6f04-4d88-8849-16b3bc7f2749

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
attribute [local simp] ProbabilityTheory.Copula.map_eval

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (i : Fin d) :
    MeasurePreserving (fun x => x i) C.toMeasure volume :=
  ⟨measurable_pi_apply i, C.map_eval i⟩
end ProbabilityTheory.Copula
