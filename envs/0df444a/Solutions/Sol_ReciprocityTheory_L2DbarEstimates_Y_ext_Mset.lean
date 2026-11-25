-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ext_Mset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:22:51.986314+00:00
-- url     : https://prove2.me/submissions/81ea37b1-90f5-43e7-a09c-566fd59258dc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_ext


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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hE : EXTStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (la : La) (F : ι → Y → ℂ) (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤) :
    ∃ G : ι → Y → ℂ, A.IsSec la G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → G i y = F i y :=
  fn_ext A hE hD hF la F hFs hloc
end ReciprocityTheory.L2DbarEstimates.Y
