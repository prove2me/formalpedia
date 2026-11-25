-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:15.068736+00:00
-- url     : https://prove2.me/submissions/c93c99e1-433d-444f-9d52-e28d36513ae3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {Y : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)}
    (h : ∀ (U : Y.Opens) (f : Γ(Y, U)) (b₀ : V), b₀ ∈ B → ⊤ ≤ y b₀ ⁻¹ᵁ U →
      ∃ N ∈ nhds b₀, N ⊆ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun b => valAt' (y b) U f) N) :
    IsHolTo B y := by
  unfold IsHolTo
  intro U f
  have hS : IsOpen {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨N, hN, hNS, -⟩ := h U f b hb.1 hb.2
    exact Filter.mem_of_superset hN hNS
  refine ⟨hS, fun b hb => ?_⟩
  obtain ⟨N, hN, -, hd⟩ := h U f b hb.1 hb.2
  exact (hd.differentiableAt hN).differentiableWithinAt
end ReciprocityTheory.ChartRestriction.G.PullbackSections
