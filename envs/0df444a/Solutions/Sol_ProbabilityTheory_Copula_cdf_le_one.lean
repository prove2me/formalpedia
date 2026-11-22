-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:58.227817+00:00
-- url     : https://prove2.me/submissions/dc81c686-3ccc-428b-8497-1998fbb39525

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
theorem _root_.solution (C : Copula d) (u : Fin d → I) : C.cdf u ≤ 1 :=
  measureReal_le_one
end ProbabilityTheory.Copula
