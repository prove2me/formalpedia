-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.pot_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:19.346982+00:00
-- url     : https://prove2.me/submissions/1469ef67-141d-4a9f-aaca-4a7ad84e61b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {L : HermLine ι} (hL : IsSmoothHerm L) {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y := by
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hL.contDiffAt (isOpen_blockNonzero.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγr : ContDiffAt ℝ 2 γ y := (hγ.contDiffAt (n := 2)).restrict_scalars ℝ
  exact (hh.comp y hγr).log (L.pos _ hy).ne'
end ReciprocityTheory.ChartRestriction.G.Geo
