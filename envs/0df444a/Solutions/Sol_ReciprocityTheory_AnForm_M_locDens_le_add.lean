-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDens_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:35.267554+00:00
-- url     : https://prove2.me/submissions/ecff9572-ad92-4c51-8e53-9b83300eddc6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Theorems.Thm_ReciprocityTheory_AnForm_M_pot_contDiffAt_two
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_locPot_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_re_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Θ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPsh A (Θ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y ≤ locDens A (fun i => Φ i + Θ i) j y := by
  unfold locDens maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _
    (fun k => hessC_locPot_posSemidef (hΦ k) (hΦp k) j hy) fun k => ?_) (by positivity)
  show (hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y -
    hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef
  rw [ReciprocityTheory.AnForm.A.hessC_add (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
    (fun y' => (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y (pot_contDiffAt_two (hΦ k) _ j hy ((Φ k).mem_U _))
    (pot_contDiffAt_two (hΘ k) _ j hy ((Θ k).mem_U _)), add_sub_cancel_left]
  exact hessC_locPot_posSemidef (hΘ k) (hΘp k) j hy
end ReciprocityTheory.AnForm.M
