-- Prove2me | solution 1 for QPK.Bru.Eset_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:49.686436+00:00
-- url     : https://prove2.me/submissions/e4396709-4737-4061-9afc-66ea18eb5f93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
import Theorems.Thm_QPK_Bru_gf_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
open QPK.Bru
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK.Bru
theorem _root_.solution (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n))
    (n : ℕ) : MeasurableSet (Eset μ K n) := by
  have h1 : MeasurableSet {x | gf μ K n x ≠ 0} :=
    (gf_meas μ K hK n) (measurableSet_singleton 0).compl
  have h2 : MeasurableSet {x | ∀ k < n, gf μ K k x = 0} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (gf_meas μ K hK k) (measurableSet_singleton 0)
  exact h1.inter h2
end QPK.Bru
