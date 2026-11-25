-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.FT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:59.332889+00:00
-- url     : https://prove2.me/submissions/b2c95933-36b5-4eda-8fb6-30eafa8055b7

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_pr
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_pr_comm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_ch


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {h m : (ι → ℂ) → ℂ} (hh : Integrable h) (hm : Integrable m) : ∫ t, FT h t * m t = ∫ x, h x * FT m x := by
  have hi : Integrable (fun q : (ι → ℂ) × (ι → ℂ) => ch (-pr q.2 q.1) * (m q.1 * h q.2)) (volume.prod volume) := by
    refine (hm.mul_prod hh).bdd_mul (c := 1) ?_ (Eventually.of_forall fun q => (norm_ch _).le)
    exact (continuous_ch.comp (continuous_pr.comp continuous_swap).neg).aestronglyMeasurable
  calc ∫ t, FT h t * m t = ∫ t, ∫ x, ch (-pr x t) * (m t * h x) := by
        congr 1; funext t; rw [FT, ← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ x, ∫ t, ch (-pr x t) * (m t * h x) := integral_integral_swap hi
    _ = _ := by
        congr 1; funext x; rw [FT, ← integral_const_mul]; congr 1; funext t; rw [pr_comm]; ring
end PositivityTheory.ThKG.Loc.Bump
