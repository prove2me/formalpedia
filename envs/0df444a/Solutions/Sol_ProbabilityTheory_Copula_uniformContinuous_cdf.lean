-- Prove2me | solution 1 for ProbabilityTheory.Copula.uniformContinuous_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:49:23.318924+00:00
-- url     : https://prove2.me/submissions/34131288-ecd2-465c-b286-38a641a09bd6

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Theorems.Thm_ProbabilityTheory_Copula_lipschitzWith_cdf

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) : UniformContinuous C.cdf :=
  C.lipschitzWith_cdf.uniformContinuous
end ProbabilityTheory.Copula
