-- Prove2me | solution 1 for ProbabilityTheory.Copula.frechet_lower_le_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:49:06.925809+00:00
-- url     : https://prove2.me/submissions/22bae5ec-bc3f-42c2-8b5d-55215f803afe

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Bounds
public import Theorems.Thm_ProbabilityTheory_Copula_sum_sub_dim_add_one_le_cdf
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_nonneg


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (u : Fin d → I) :
    max 0 ((∑ i, (u i : ℝ)) - d + 1) ≤ C.cdf u :=
  max_le (C.cdf_nonneg u) (C.sum_sub_dim_add_one_le_cdf u)
end ProbabilityTheory.Copula
