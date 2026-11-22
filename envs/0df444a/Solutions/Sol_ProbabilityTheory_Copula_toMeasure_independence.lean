-- Prove2me | solution 1 for ProbabilityTheory.Copula.toMeasure_independence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:32.091415+00:00
-- url     : https://prove2.me/submissions/1a863f21-e7a4-492a-9988-e0a8545d9546

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Independence

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
namespace ProbabilityTheory.Copula
theorem _root_.solution (d : ℕ) :
    (independence d).toMeasure = Measure.pi (fun _ : Fin d => (volume : Measure I)) := rfl
end ProbabilityTheory.Copula
