-- Prove2me | solution 1 for PI.VolStabW.um_D_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:38.787726+00:00
-- url     : https://prove2.me/submissions/0bbd5a2f-1a41-45b2-af7d-747b23ee4f98

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
theorem _root_.solution (Γ H : Subgroup G) (x : G) (γ : Γ) : γ • umD Γ H x = umD Γ H x := by
  ext y
  constructor
  · rintro ⟨z, ⟨γ', hγ', h, hh, rfl⟩, rfl⟩
    exact ⟨γ * γ', Γ.mul_mem γ.2 hγ', h, hh, by show (γ : G) * (γ' * x * h) = _; group⟩
  · rintro ⟨γ', hγ', h, hh, rfl⟩
    refine ⟨(γ : G)⁻¹ * γ' * x * h, ⟨(γ : G)⁻¹ * γ', Γ.mul_mem (Γ.inv_mem γ.2) hγ', h, hh, rfl⟩, ?_⟩
    show (γ : G) * ((γ : G)⁻¹ * γ' * x * h) = _
    group
end PI.VolStabW
