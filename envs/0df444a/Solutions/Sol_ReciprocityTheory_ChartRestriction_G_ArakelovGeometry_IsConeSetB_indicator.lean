-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsConeSetB.indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:03.931334+00:00
-- url     : https://prove2.me/submissions/c3179777-4252-4de4-8c11-33fd614bef3b

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
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace IsConeSetB
theorem _root_.solution {s : Set (Ix κ → ℂ)} (hs : IsConeSetB s) {f : (Ix κ → ℂ) → ℝ}
    (hf : IsDegZero f) : IsDegZero (s.indicator f) := fun c z hc => by
  show s.indicator f (c • z) = s.indicator f z
  by_cases h : z ∈ s
  · rw [Set.indicator_of_mem ((hs c z hc).2 h), Set.indicator_of_mem h, hf c z hc]
  · rw [Set.indicator_of_notMem (fun h' => h ((hs c z hc).1 h')), Set.indicator_of_notMem h]
end IsConeSetB
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
