-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_mem_mcPts_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:54.124232+00:00
-- url     : https://prove2.me/submissions/a0cce7cf-8334-4154-a897-ad69ce47fc11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} :
    z ∈ mcPts (ι := GlobalTheory κ) P ↔ z ∈ pts P := by
  simp only [mcPts, pts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, h⟩
    obtain ⟨i, hi⟩ := hk ()
    refine ⟨fun h0 => hi (by simp [h0]), h⟩
  · rintro ⟨hz, h⟩
    refine ⟨fun k => ?_, h⟩
    by_contra hc
    push_neg at hc
    exact hz (funext fun p => hc p.2)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
