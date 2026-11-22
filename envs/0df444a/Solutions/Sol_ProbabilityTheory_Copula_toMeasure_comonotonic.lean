-- Prove2me | solution 1 for ProbabilityTheory.Copula.toMeasure_comonotonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:57.774165+00:00
-- url     : https://prove2.me/submissions/8c889d2a-44a0-41a5-9379-23bb5678562a

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Comonotonic

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
namespace ProbabilityTheory.Copula
theorem _root_.solution (d : ℕ) :
    (comonotonic d).toMeasure =
      (volume : Measure I).map (fun u (_ : Fin d) => u) := rfl
end ProbabilityTheory.Copula
