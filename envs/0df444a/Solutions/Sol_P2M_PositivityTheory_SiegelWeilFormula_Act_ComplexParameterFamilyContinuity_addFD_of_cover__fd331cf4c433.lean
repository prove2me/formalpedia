-- Prove2me | solution 1 for P2M_PositivityTheory_SiegelWeilFormula_Act_ComplexParameterFamilyContinuity_addFD_of_cover__fd331cf4c433
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:00.479863+00:00
-- url     : https://prove2.me/submissions/6335ca4c-8665-4037-be51-5506cda09c41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_AddFDOfCover
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_ComplexParameterFamilyContinuity_addFD_of_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
theorem _root_.solution {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [DiscreteTopology Γ] {C : Set A} (hC : IsCompact C)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ C) (μ : Measure A) :
    ∃ 𝓕 : Set A, IsAddFundamentalDomain Γ 𝓕 μ ∧ IsCompact (closure 𝓕) := by
  obtain ⟨𝓕, hm, hc, hu⟩ := addFD_of_cover Γ hC hcov
  exact ⟨𝓕, IsAddFundamentalDomain.mk' hm.nullMeasurableSet hu, hc⟩
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
