-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:09.503894+00:00
-- url     : https://prove2.me/submissions/81b5b225-45e9-473b-874f-201fa10bfcd7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_cml_perm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_eq

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) {l l' : List V} (p : l.Perm l') :
    lD φ x l = lD φ x l' := by
  have hl : l'.length = l.length := p.length_eq.symm
  rw [lD_eq φ x l rfl, lD_eq φ x l' hl]
  exact cml_perm p l.length _ (fun v σ => (hφ.of_le le_top).iteratedFDeriv_comp_perm v σ) rfl hl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
