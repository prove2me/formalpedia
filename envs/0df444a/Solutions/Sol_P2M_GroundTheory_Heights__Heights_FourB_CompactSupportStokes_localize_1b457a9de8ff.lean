-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_localize_1b457a9de8ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:52.124543+00:00
-- url     : https://prove2.me/submissions/f123f55b-99a6-4c6f-a567-f22ee5c675b9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chartMove_a20e02d4b768

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
theorem _root_.solution (A : FinHolAtlas e X) (χ : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (g : X → ℝ)
    (hs : ∀ k, ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ (A.chart j).source →
      g ((A.chart k).symm y) * locDens A Φ k y = 0)
    (hint : ∀ k, IntegrableOn (fun y => χ.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target) :
    integralWith A χ Φ g =
      ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Φ j y := by
  unfold integralWith
  rw [Finset.sum_congr rfl (fun k _ => chartMove A χ Φ hΦ j k g (hs k)),
    ← integral_finsetSum _ (fun k _ => hint k)]
  refine setIntegral_congr_fun (A.chart j).open_target.measurableSet (fun y _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul, χ.sum_eq_one, one_mul]
end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
