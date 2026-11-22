-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_le_frechet_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:45:53.901755+00:00
-- url     : https://prove2.me/submissions/9ab06d68-0455-4ed5-b3f5-5b4deb3a0c24

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Bounds
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_le_coord
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_le_one
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
    C.cdf u ≤ ((⨅ i, u i : I) : ℝ) := by
  have h : (⟨C.cdf u, C.cdf_nonneg u, C.cdf_le_one u⟩ : I) ≤ ⨅ i, u i :=
    le_iInf fun i => C.cdf_le_coord u i
  exact h
end ProbabilityTheory.Copula
