-- Prove2me | solution 1 for ProbabilityTheory.Copula.existsUnique_sklarCopula_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:51:50.927025+00:00
-- url     : https://prove2.me/submissions/5802992f-0352-4a58-bef5-d0916e88ff06

module
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous
public import Theorems.Thm_ProbabilityTheory_Copula_isSklarCopula_ofContinuousMarginals
public import Theorems.Thm_ProbabilityTheory_Copula_IsSklarCopula_unique

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (μ : ProbabilityMeasure (Fin d → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i))) :
    ∃! C : Copula d, IsSklarCopula μ C := by
  refine ⟨ofContinuousMarginals μ hc, isSklarCopula_ofContinuousMarginals μ hc, ?_⟩
  intro C hC
  exact hC.unique hc (isSklarCopula_ofContinuousMarginals μ hc)
end ProbabilityTheory.Copula
