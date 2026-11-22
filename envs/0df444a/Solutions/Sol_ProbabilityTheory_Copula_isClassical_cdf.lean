-- Prove2me | solution 1 for ProbabilityTheory.Copula.isClassical_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:52:35.706846+00:00
-- url     : https://prove2.me/submissions/6810ac0a-1fed-4802-bfc7-c8260da75195

module
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Definitions.Def_LeanPool_Copula_Unique
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_eq_zero_of_coord_eq_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_cdf_nonneg
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) : IsClassical C.cdf where
  normalized := C.cdf_one
  grounded := C.cdf_eq_zero_of_coord_eq_zero
  marginal := C.cdf_update_one
  increasing := C.rectangleIncrement_cdf_nonneg
end ProbabilityTheory.Copula
