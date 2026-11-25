-- Prove2me | solution 1 for QPK.Bru.bf_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:12.463862+00:00
-- url     : https://prove2.me/submissions/df6bc859-2055-4eef-a842-c106bca4aae8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
import Theorems.Thm_QPK_Bru_gf_meas
import Theorems.Thm_QPK_Bru_Eset_meas

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
theorem _root_.solution (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) :
    Measurable (bf μ K) := by
  unfold bf
  refine Measurable.ennreal_tsum fun n => ?_
  refine Measurable.indicator ?_ (Eset_meas μ K hK n)
  exact (measurable_one.indicator (hK n).measurableSet).mul (gf_meas μ K hK n).inv
end QPK.Bru
