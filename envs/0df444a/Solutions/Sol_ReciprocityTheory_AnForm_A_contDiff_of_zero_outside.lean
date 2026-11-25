-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.contDiff_of_zero_outside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:06.502984+00:00
-- url     : https://prove2.me/submissions/620ec249-5e07-4608-9f93-fb9fd95c2f32

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {f : (Fin D → ℂ) → ℂ} {U K : Set (Fin D → ℂ)}
    {m : WithTop ℕ∞} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hf : ContDiffOn ℝ m f U)
    (h0 : ∀ y ∉ K, f y = 0) : ContDiff ℝ m f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∈ Kᶜ := (Set.mem_compl_iff _ _).2 fun h => hy (hKU h)
    have hev : f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hyK] with z hz
      exact h0 z ((Set.mem_compl_iff _ _).1 hz)
    exact contDiffAt_const.congr_of_eventuallyEq hev
end ReciprocityTheory.AnForm.A
