-- Prove2me | solution 1 for PI.VolStabW.um_smulInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:01.16626+00:00
-- url     : https://prove2.me/submissions/62b6ff1e-782d-4cb5-8fa3-e5cdda120382

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabW
theorem _root_.solution (Γ : Subgroup G) (μ : Measure G) [IsMulLeftInvariant μ] :
    SMulInvariantMeasure Γ G μ :=
  ⟨fun γ s _ => by
    have : (fun x : G => γ • x) = fun x => (γ : G) * x := rfl
    rw [this]
    exact measure_preimage_mul μ γ s⟩
end PI.VolStabW
