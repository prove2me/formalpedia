-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsClassical.continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:58:42.756589+00:00
-- url     : https://prove2.me/submissions/4f92582e-f2b0-40f1-89fd-7738f0727819

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_lipschitzWith

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
namespace IsClassical
theorem _root_.solution (hF : IsClassical F) : Continuous F := hF.lipschitzWith.continuous
end IsClassical
end ProbabilityTheory.Copula
