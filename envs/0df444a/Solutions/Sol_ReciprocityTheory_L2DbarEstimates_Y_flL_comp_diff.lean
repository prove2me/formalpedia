-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flL_comp_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:55.586224+00:00
-- url     : https://prove2.me/submissions/8dadf191-701e-47d9-898e-c283cfb20d62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (i : ι) (k : Fin n) :
    DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v))
      (flO A w0 i) := by

  have hw := hD.isSection_denom
  have hs := hD.sec_s k
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at hw hs
  have h1 : DifferentiableOn ℂ (s k i ∘ (A.chart i).symm) (flO A w0 i) :=
    (hs.1 i).mono (fun v hv => ⟨hv.1, Set.mem_univ _⟩)
  have h2 : DifferentiableOn ℂ (w0 i ∘ (A.chart i).symm) (flO A w0 i) :=
    (hw.1 i).mono (fun v hv => ⟨hv.1, Set.mem_univ _⟩)
  have h3 : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) * (w0 i ((A.chart i).symm v))⁻¹)
      (flO A w0 i) := DifferentiableOn.mul h1 (DifferentiableOn.inv h2 (fun v (hv : v ∈ flO A w0 i) => hv.2))
  simpa only [div_eq_mul_inv] using h3
end ReciprocityTheory.L2DbarEstimates.Y
