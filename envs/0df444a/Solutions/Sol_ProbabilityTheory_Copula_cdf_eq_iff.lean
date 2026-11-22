-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:49:41.41367+00:00
-- url     : https://prove2.me/submissions/d78208d4-93e5-418d-a6c5-bd3d9c3bb0bb

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_injective

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution {C D : Copula d} : C.cdf = D.cdf ↔ C = D :=
  cdf_injective.eq_iff
end ProbabilityTheory.Copula
