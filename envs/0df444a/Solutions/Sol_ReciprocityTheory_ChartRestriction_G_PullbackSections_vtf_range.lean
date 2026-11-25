-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:49.177417+00:00
-- url     : https://prove2.me/submissions/b1aedc63-006e-454d-923f-9eb4c76273a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_mem

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
open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Set.range x ⊆ Set.range U.ι := by
  rintro _ ⟨q, rfl⟩
  rw [Scheme.Opens.range_ι, vtf_pt_eq q]
  exact vtf_mem h
end ReciprocityTheory.ChartRestriction.G.PullbackSections
