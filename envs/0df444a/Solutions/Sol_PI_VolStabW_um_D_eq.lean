-- Prove2me | solution 1 for PI.VolStabW.um_D_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:45.138287+00:00
-- url     : https://prove2.me/submissions/e27aa4b9-39c5-4840-8900-d3c1e7ce35c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Theorems.Thm_PI_VolStabW_um_D_subset

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
theorem _root_.solution (Γ H : Subgroup G) {x z : G} (hz : z ∈ umD Γ H x) : umD Γ H z = umD Γ H x := by
  refine (um_D_subset Γ H hz).antisymm (um_D_subset Γ H ?_)
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hz
  exact ⟨γ⁻¹, Γ.inv_mem hγ, h⁻¹, H.inv_mem hh, by group⟩
end PI.VolStabW
