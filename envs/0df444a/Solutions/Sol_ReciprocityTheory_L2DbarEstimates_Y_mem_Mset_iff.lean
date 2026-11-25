-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.mem_Mset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:44:54.596836+00:00
-- url     : https://prove2.me/submissions/8cc6955f-6009-4e53-ad96-c6db3ed259d8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec

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
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*}
    [AddCommGroup La] {A : WeightedAtlas n Y ι La} {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (De : MvPolynomial (Fin n) ℂ)
    (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    y ∈ A.Mset w0 s De ↔
      w0 i y ≠ 0 ∧ MvPolynomial.eval (fun k => s k i y / w0 i y) De ≠ 0 := by
  have hg := A.g_ne L (A.pick y) i y (A.mem_pick y) hy
  have hw : w0 (A.pick y) y = A.g L (A.pick y) i y * w0 i y :=
    hD.isSection_denom.2 _ _ y trivial (A.mem_pick y) hy
  have hs : ∀ k, s k (A.pick y) y = A.g L (A.pick y) i y * s k i y := fun k =>
    (hD.sec_s k).2 _ _ y trivial (A.mem_pick y) hy
  have hz : (fun k => A.zmap w0 s y k) = fun k => s k i y / w0 i y := by
    funext k
    show s k (A.pick y) y / w0 (A.pick y) y = _
    rw [hs k, hw, mul_div_mul_left _ _ hg]
  show (w0 (A.pick y) y ≠ 0 ∧ MvPolynomial.eval (fun k => A.zmap w0 s y k) De ≠ 0) ↔ _
  rw [hz, hw]
  simp [hg]
end ReciprocityTheory.L2DbarEstimates.Y
