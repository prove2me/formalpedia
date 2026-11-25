-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolFam_vtfLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:04.661972+00:00
-- url     : https://prove2.me/submissions/45040151-543b-47f5-807c-2180392826b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_local

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
variable {g : ℕ} {X Y : Scheme.{0}} (f : Y ⟶ X) (u : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
  (he : ∀ z, e z ≫ f = u)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (hol : IsHolFam e) : IsHolFam (vtfLift f u e he) := by
  intro V φ
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro z0 hz0
    obtain ⟨N, hN, hzN, hNS, -⟩ := vtf_local f u e he hol V φ z0 hz0
    exact Filter.mem_of_superset (hN.mem_nhds hzN) hNS
  · intro z0 hz0
    obtain ⟨N, hN, hzN, -, hd⟩ := vtf_local f u e he hol V φ z0 hz0
    exact ((hd z0 hzN).differentiableAt (hN.mem_nhds hzN)).differentiableWithinAt
end ReciprocityTheory.ChartRestriction.G.PullbackSections
