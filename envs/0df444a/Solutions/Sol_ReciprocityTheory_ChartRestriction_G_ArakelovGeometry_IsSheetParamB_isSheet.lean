-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsSheetParamB.isSheet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:38:02.733516+00:00
-- url     : https://prove2.me/submissions/93ccec6a-cb04-41cf-b9aa-af09f2480cbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adb_mem_mcPts_iff

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
namespace IsSheetParamB
theorem _root_.solution (hs : IsSheetParamB P Ψ U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    IsSheet P Ψ y (segre (ι := GlobalTheory κ) (γ y)) γ := by
  obtain ⟨⟨hU, hγ, hpts, -⟩, hΨ⟩ := hs
  refine ⟨rfl, ?_⟩
  filter_upwards [hU.mem_nhds hy] with y' hy'
  exact ⟨(hγ y' hy').differentiableAt, adb_mem_mcPts_iff.2 (hpts y' hy'), hΨ y' hy'⟩
end IsSheetParamB
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
