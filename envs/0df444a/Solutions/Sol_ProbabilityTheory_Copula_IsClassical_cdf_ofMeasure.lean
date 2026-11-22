-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsClassical.cdf_ofMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:51:26.191537+00:00
-- url     : https://prove2.me/submissions/c8869d7b-942e-4cb7-8d68-860ffa1cce02

module
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Definitions.Def_LeanPool_Copula_Unique
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Basic

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
namespace IsClassical
theorem _root_.solution {F : (Fin d → I) → ℝ} (hF : IsClassical F)
    (μ : ProbabilityMeasure (Fin d → I)) (hμ : ∀ u, μ.toMeasure.real (Iic u) = F u) :
    (hF.ofMeasure μ hμ).cdf = F := funext hμ
end IsClassical
end ProbabilityTheory.Copula
