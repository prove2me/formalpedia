-- Prove2me | solution 1 for ProbabilityTheory.Copula.continuous_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:49:22.8422+00:00
-- url     : https://prove2.me/submissions/2b50dd9f-14fc-45a7-952d-97b1fb2055fe

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
theorem _root_.solution (C : Copula d) : Continuous C.cdf :=
  C.lipschitzWith_cdf.continuous
end ProbabilityTheory.Copula
