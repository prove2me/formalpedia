-- Prove2me | solution 1 for ProbabilityTheory.Copula.unique_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:51:25.673704+00:00
-- url     : https://prove2.me/submissions/bcc73e77-87f3-465b-b105-be50d4898fd6

module
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Definitions.Def_LeanPool_Copula_Unique
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_injective


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (F : (Fin d → I) → ℝ) {C D : Copula d}
    (hC : C.cdf = F) (hD : D.cdf = F) : C = D :=
  cdf_injective (hC.trans hD.symm)
end ProbabilityTheory.Copula
