-- Prove2me | solution 1 for PI.VolStabSW.um_D_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:10.14543+00:00
-- url     : https://prove2.me/submissions/edf55ec1-57ec-448b-a303-10a4ffdc50a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod

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
theorem _root_.solution (Γ H : Subgroup G) (hH : IsOpen (H : Set G)) (x : G) :
    IsOpen (umD Γ H x) := by
  have e : umD Γ H x = ⋃ γ ∈ Γ, (fun h => γ * x * h) '' (H : Set G) := by
    ext y
    simp only [umD, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, h, hh, rfl⟩
      exact ⟨γ, hγ, h, hh, rfl⟩
    · rintro ⟨γ, hγ, h, hh, rfl⟩
      exact ⟨γ, hγ, h, hh, rfl⟩
  rw [e]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * x) _ hH
end PI.VolStabSW
