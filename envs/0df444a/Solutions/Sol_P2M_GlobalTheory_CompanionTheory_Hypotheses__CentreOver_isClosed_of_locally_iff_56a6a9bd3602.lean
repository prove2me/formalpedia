-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_of_locally_iff_56a6a9bd3602
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:38.449535+00:00
-- url     : https://prove2.me/submissions/6768e6ca-c4cd-498d-a549-fd9f354e4154

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmoothStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPairStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {T : Type*} [TopologicalSpace T] {C : Set T} (hC : IsClosed C)
    (P : T → Prop) (h : ∀ x ∈ C, ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ C → (P y ↔ P x)) :
    IsClosed {x | x ∈ C ∧ P x} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxC : x ∈ C
  · obtain ⟨V, hV, hxV, hy⟩ := h x hxC
    refine ⟨V, fun y hyV hyS => hx ⟨hxC, (hy y hyV hyS.1).1 hyS.2⟩, hV, hxV⟩
  · exact ⟨Cᶜ, fun y hy hyS => hy hyS.1, hC.isOpen_compl, hxC⟩
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
