-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:13.066224+00:00
-- url     : https://prove2.me/submissions/86144fb2-7530-4097-889e-f96d96341242

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp

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
theorem _root_.solution (Θ : W → ℂ) (w : σ → W) (Φ : Multiset W → MvPowerSeries σ ℂ)
    (hd : ∀ q s, pderiv ℂ q (Φ s) = Φ (w q ::ₘ s)) (hc : ∀ s, constantCoeff (Φ s) = mD Θ 0 s) :
    IsTayF Θ w (Φ 0) := by
  have key : ∀ l : List σ, l.foldr (fun q H => pderiv ℂ q H) (Φ 0) = Φ ((l.map w : List W) : Multiset W) := by
    intro l
    induction l with
    | nil => rfl
    | cons q l ih => simp only [List.foldr_cons, ih, hd, List.map_cons, Multiset.cons_coe]
  intro l
  rw [key, hc]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
