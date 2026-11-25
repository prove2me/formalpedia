-- Prove2me | solution 1 for PI.VolStabW.um_D_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:41.366344+00:00
-- url     : https://prove2.me/submissions/e1357963-2f2f-410b-bac2-ad2c40bb4f52

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
theorem _root_.solution (Γ H : Subgroup G) {x z : G} (hz : z ∈ umD Γ H x) :
    umD Γ H z ⊆ umD Γ H x := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hz
  rintro y ⟨γ', hγ', h', hh', rfl⟩
  exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, h * h', H.mul_mem hh hh', by group⟩
end PI.VolStabW
