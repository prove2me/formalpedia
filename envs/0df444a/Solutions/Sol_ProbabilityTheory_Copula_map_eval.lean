-- Prove2me | solution 1 for ProbabilityTheory.Copula.map_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:01.648088+00:00
-- url     : https://prove2.me/submissions/f887314c-d5ea-4182-bc87-6c903521e834

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic

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
    C.toMeasure.map (fun x => x i) = volume :=
  C.marginal_eq i
end ProbabilityTheory.Copula
