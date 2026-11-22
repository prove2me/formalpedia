-- Prove2me | solution 1 for ProbabilityTheory.Copula.monotone_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:58.720563+00:00
-- url     : https://prove2.me/submissions/c8749d8c-55ef-4ee2-8fda-333947b818c5

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
theorem _root_.solution (C : Copula d) : Monotone C.cdf := by
  intro u v huv
  exact measureReal_mono (Iic_subset_Iic.mpr huv)
end ProbabilityTheory.Copula
