-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:46:51.284837+00:00
-- url     : https://prove2.me/submissions/9e1eb5ce-a820-4724-97db-605df5d8f64a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_mD_comp

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
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0)
    (A : W →L[ℂ] V) {w : σ → W} {v : σ → V} (hv : ∀ q, A (w q) = v q) {F : MvPowerSeries σ ℂ}
    (hF : IsTayF f v F) : IsTayF (f ∘ A) w F := by
  intro l
  have hAw : (⇑A ∘ w) = v := funext hv
  rw [hF l, mD_comp hf A, Multiset.map_coe, List.map_map, hAw]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
