-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsSklarCopula.cdf_eq_on_ranges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:44.400179+00:00
-- url     : https://prove2.me/submissions/32faba10-7842-4fa0-8e77-d7f5c44efec5

module
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
namespace IsSklarCopula
theorem _root_.solution {μ : ProbabilityMeasure (Fin d → ℝ)} {C D : Copula d}
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula μ D) (u : Fin d → I)
    (hu : ∀ i, u i ∈ Set.range (cdfUnit (marginal μ i))) : C.cdf u = D.cdf u := by
  choose x hx using hu
  have hux : marginalTransform μ x = u := funext hx
  rw [← hux, hC x, hD x]
end IsSklarCopula
end ProbabilityTheory.Copula
