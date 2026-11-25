-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_chart_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:52.330604+00:00
-- url     : https://prove2.me/submissions/d8a8e64b-2f36-46b2-b128-e720525cbc1b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_isOpen_O

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x),
      ((e.symm (A.zLoc w0 s i v) : A.Mset w0 s De) : Y) = (A.chart i).symm v := by
  have hO := fc_isOpen_O A (De := De) hD i
  have hmO : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
    refine ⟨(A.chart i).map_source hxi, ?_⟩
    show (A.chart i).symm (A.chart i x) ∈ A.Mset w0 s De
    rw [(A.chart i).left_inv hxi]
    exact x.2
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.mp e.open_source
  have hxU : (x : Y) ∈ U := by
    have hx : x ∈ Subtype.val ⁻¹' U := by rw [hUe]; exact hxe
    exact hx
  have hcont : ∀ᶠ v in 𝓝 (A.chart i x), (A.chart i).symm v ∈ U := by
    apply ((A.chart i).continuousAt_symm ((A.chart i).map_source hxi)).preimage_mem_nhds
    rw [(A.chart i).left_inv hxi]
    exact hU.mem_nhds hxU
  filter_upwards [hO.mem_nhds hmO, hcont] with v hvO hvU
  have hp : (⟨(A.chart i).symm v, hvO.2⟩ : A.Mset w0 s De) ∈ e.source := by
    rw [← hUe]
    exact hvU
  have hz : A.zLoc w0 s i v = e ⟨(A.chart i).symm v, hvO.2⟩ := by
    rw [fc_zLoc_eq A hD i v hvO.1]
    exact he hp
  rw [hz, e.left_inv hp]
end ReciprocityTheory.L2DbarEstimates.Y
