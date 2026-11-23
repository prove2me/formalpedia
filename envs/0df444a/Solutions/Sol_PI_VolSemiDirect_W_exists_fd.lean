-- Prove2me | solution 1 for PI.VolSemiDirect.W.exists_fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:39.784745+00:00
-- url     : https://prove2.me/submissions/26eb1cdb-031d-4e9b-af79-cd7e90d41d08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Theorems.Thm_PI_VolSemiDirect_W_exists_sfd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory
namespace PI.VolSemiDirect.W
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ μ : Measure G, IsFundamentalDomain Λ 𝓕 μ := by
  obtain ⟨F, hF, hex⟩ := exists_sfd Λ
  exact ⟨F, hF, fun μ => IsFundamentalDomain.mk' hF.nullMeasurableSet hex⟩
end PI.VolSemiDirect.W
