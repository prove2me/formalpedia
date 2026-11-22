-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:26.950469+00:00
-- url     : https://prove2.me/submissions/4651bfdc-16e4-4592-8133-1cd59c068471

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_CDF

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (u : Fin d → I) : 0 ≤ C.cdf u :=
  measureReal_nonneg
end ProbabilityTheory.Copula
