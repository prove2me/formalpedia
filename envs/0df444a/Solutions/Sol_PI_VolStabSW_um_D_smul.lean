-- Prove2me | solution 1 for PI.VolStabSW.um_D_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:46.074943+00:00
-- url     : https://prove2.me/submissions/fd141648-1f8b-4257-afc6-82969d23cc38

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
theorem _root_.solution (Γ H : Subgroup G) (x : G) (γ : Γ) : γ • umD Γ H x = umD Γ H x := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [umD, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
  constructor
  · rintro ⟨δ, hδ, h, hh, e⟩
    refine ⟨(γ : G) * δ, Γ.mul_mem γ.2 hδ, h, hh, ?_⟩
    have e2 : y = (γ : G) * ((γ : G)⁻¹ * y) := by group
    rw [e2, e]
    simp only [mul_assoc]
  · rintro ⟨δ, hδ, h, hh, rfl⟩
    exact ⟨(γ : G)⁻¹ * δ, Γ.mul_mem (Γ.inv_mem γ.2) hδ, h, hh, by simp only [mul_assoc, inv_mul_cancel_left]⟩
end PI.VolStabSW
