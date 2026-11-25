-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.iter_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:21.348062+00:00
-- url     : https://prove2.me/submissions/865e1aef-3fc0-49d3-b4c1-bd3a5cccc383

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
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : W →L[ℂ] V) (i : ℕ) :
    iteratedFDeriv ℂ i (f ∘ A) 0 = (iteratedFDeriv ℂ i f 0).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := ω) le_rfl (fun _ => rfl)
  obtain ⟨U, hUu, hUo, h0U⟩ := mem_nhds_iff.mp hu
  have hfU : ContDiffOn ℂ ω f U := hfu.mono hUu
  have hAo : IsOpen (A ⁻¹' U) := hUo.preimage A.continuous
  have h0A : (0 : W) ∈ A ⁻¹' U := by simpa using h0U
  have key := A.iteratedFDerivWithin_comp_right hfU hUo.uniqueDiffOn hAo.uniqueDiffOn
    (x := 0) (by simpa using h0U) (i := i) le_top
  rw [map_zero] at key
  rw [iteratedFDerivWithin_of_isOpen i hAo h0A, iteratedFDerivWithin_of_isOpen i hUo h0U] at key
  exact key
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
