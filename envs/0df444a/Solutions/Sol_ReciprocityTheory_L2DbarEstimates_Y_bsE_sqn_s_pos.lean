-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsE_sqn_s_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:48.388083+00:00
-- url     : https://prove2.me/submissions/138b4eda-a601-4f75-ae6c-dc921c77e161

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsC_sqn_ratio
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsD_pos


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
    {x : Y} (hx : x ∈ A.Mset w0 s De) : 0 < A.sqn L s x := by
  obtain ⟨ha, -, hZ, -, -⟩ := bsD_pos A hD hF hσ hX x hx
  rw [bsC_sqn_ratio A L s w0 x hx.1]; positivity
end ReciprocityTheory.L2DbarEstimates.Y
