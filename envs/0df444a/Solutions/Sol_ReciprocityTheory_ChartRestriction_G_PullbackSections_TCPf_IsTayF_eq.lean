-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.IsTayF.eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:05.255222+00:00
-- url     : https://prove2.me/submissions/62a5e5ab-d0d2-473e-aa90-cbb41c4b3cbe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_eq_of_cc

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {σ : Type}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
namespace IsTayF
theorem _root_.solution {Θ : W → ℂ} {w : σ → W} {F G : MvPowerSeries σ ℂ} (hF : IsTayF Θ w F)
    (hG : IsTayF Θ w G) : F = G := eq_of_cc F G fun l => (hF l).trans (hG l).symm
end IsTayF
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
