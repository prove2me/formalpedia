-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_mem_coneOver_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:19.406415+00:00
-- url     : https://prove2.me/submissions/d0bec6f3-1c38-4809-b4fe-884472977acf

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
theorem _root_.solution {y : Fin D → ℂ} (hy : y ∈ U) : γ y ∈ coneOver U γ :=
  ⟨y, hy, 1, one_ne_zero, by simp⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
