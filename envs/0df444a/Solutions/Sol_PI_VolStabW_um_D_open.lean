-- Prove2me | solution 1 for PI.VolStabW.um_D_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:35.851271+00:00
-- url     : https://prove2.me/submissions/3bf36774-e923-4c67-9a0d-78978e8986b8

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
theorem _root_.solution (Γ H : Subgroup G) (hH : IsOpen (H : Set G)) (x : G) :
    IsOpen (umD Γ H x) := by
  have : umD Γ H x = ⋃ γ : Γ, (fun z => (γ : G) * x * z) '' (H : Set G) := by
    ext y
    simp only [umD, mem_ofPred_eq, mem_iUnion, mem_image, SetLike.mem_coe, Subtype.exists,
      exists_prop]
    constructor
    · rintro ⟨γ, hγ, h, hh, rfl⟩
      exact ⟨γ, hγ, h, hh, rfl⟩
    · rintro ⟨γ, hγ, h, hh, rfl⟩
      exact ⟨γ, hγ, h, hh, rfl⟩
  rw [this]
  refine isOpen_iUnion fun γ => ?_
  have : (fun z => (γ : G) * x * z) = (Homeomorph.mulLeft ((γ : G) * x)) := rfl
  rw [this]
  exact (Homeomorph.mulLeft ((γ : G) * x)).isOpenMap _ hH
end PI.VolStabW
