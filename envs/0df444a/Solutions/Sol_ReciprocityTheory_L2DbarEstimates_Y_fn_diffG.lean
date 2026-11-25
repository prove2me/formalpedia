-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_diffG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:02.916702+00:00
-- url     : https://prove2.me/submissions/aa9302b9-bb09-4cd0-9e10-56bf9d9c3450

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffOn_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (i : ι) :
    DifferentiableOn ℂ (fnG A w0 s De i) (A.chart i).target := by
  obtain ⟨h0, -⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hw : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) (A.chart i).target := by
    have := h0 i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  have hs : ∀ k, DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) (A.chart i).target := by
    intro k
    obtain ⟨hk, -⟩ : A.IsSecOn L Set.univ (s k) := hD.sec_s k
    have := hk i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  exact fn_diffOn_hom De hw hs
end ReciprocityTheory.L2DbarEstimates.Y
