-- Prove2me | solution 1 for ProbabilityTheory.Copula.isClassical_iff_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T19:00:40.88873+00:00
-- url     : https://prove2.me/submissions/871e5b20-db7c-4b5c-b89f-8f2df42229b1

module
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Characterization
public import Theorems.Thm_ProbabilityTheory_Copula_isClassical_cdf


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
theorem _root_.solution : IsClassical F ↔ ∃! C : Copula d, C.cdf = F := by
  refine ⟨IsClassical.existsUnique, ?_⟩
  rintro ⟨C, rfl, _⟩
  exact C.isClassical_cdf
end ProbabilityTheory.Copula
