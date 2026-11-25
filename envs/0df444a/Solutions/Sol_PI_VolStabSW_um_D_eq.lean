-- Prove2me | solution 1 for PI.VolStabSW.um_D_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:41.700362+00:00
-- url     : https://prove2.me/submissions/11a60143-28ef-40d7-81ff-d47c769ad4ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod
import Theorems.Thm_PI_VolStabSW_um_D_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabSW
theorem _root_.solution (Γ H : Subgroup G) {x z : G} (hz : z ∈ umD Γ H x) : umD Γ H z = umD Γ H x := by
  apply Set.Subset.antisymm (um_D_subset Γ H hz)
  apply um_D_subset Γ H
  simp only [umD, Set.mem_setOf_eq] at hz ⊢
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hz
  exact ⟨γ⁻¹, Γ.inv_mem hγ, h⁻¹, H.inv_mem hh, by group⟩
end PI.VolStabSW
