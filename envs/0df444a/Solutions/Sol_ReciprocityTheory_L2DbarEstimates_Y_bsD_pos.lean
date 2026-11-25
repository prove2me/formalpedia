-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsD_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:34.518655+00:00
-- url     : https://prove2.me/submissions/ea115f8f-7c4a-49d9-ac61-55f8ec825c15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsB_z_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_jz_det_ne


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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn mu0 (A.Mset w0 s De) σ) (hX : ∃ i0 : Fin n, MvPolynomial.X i0 ∣ De)
    (x : Y) (hx : x ∈ A.Mset w0 s De) :
    0 < A.nsq L w0 x ∧ 0 < A.nsq mu0 σ x ∧
      0 < ∑ k, ‖s k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      0 < ∑ k, ‖w k (A.pick x) x / w0 (A.pick x) x‖ ^ 2 ∧
      (jz A w0 s (A.pick x) x).det ≠ 0 := by
  obtain ⟨i0, hX0⟩ := hX
  refine ⟨bsA_nsq_pos A hx.1, bsA_nsq_pos A (hσ.2 x hx), ?_, ?_,
    jz_det_ne A hD hF x hx _ (A.mem_pick x)⟩
  · have h := bsB_z_ne A hx hX0
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i0))
    have : s i0 (A.pick x) x / w0 (A.pick x) x ≠ 0 := h
    positivity
  · obtain ⟨k, hk⟩ := hD.no_common_zero x
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ k))
    have : w k (A.pick x) x / w0 (A.pick x) x ≠ 0 := div_ne_zero hk hx.1
    positivity
end ReciprocityTheory.L2DbarEstimates.Y
