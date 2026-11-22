-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:56.852787+00:00
-- url     : https://prove2.me/submissions/f8c93003-7b02-44bc-bdf0-e522b83a6e65

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Theorems.Thm_ProbabilityTheory_Copula_ext_cdf

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution : Function.Injective (cdf (d := d)) :=
  fun _ _ h => ext_cdf (congrFun h)
end ProbabilityTheory.Copula
