-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.FT_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:48.770321+00:00
-- url     : https://prove2.me/submissions/dd590196-2757-4e21-9c51-79f43c9f27fd

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integral_scale
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_pr
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_ch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {m : (ι → ℂ) → ℂ} (hm : Integrable m) {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) (x : ι → ℂ) :
    FT (fun t => m (y * t)) x = ((nm y : ℝ) : ℂ)⁻¹ * FT m (x * y⁻¹) := by
  have h := integral_scale hy (g := fun t => ch (-pr t (x * y⁻¹)) * m t)
    ((continuous_ch.comp (continuous_pr.comp (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable.mul hm.1)
  rw [Complex.real_smul] at h
  push_cast at h
  rw [FT, FT, ← h]
  congr 1; funext t; congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  have := hy w
  simp only [Pi.mul_apply, Pi.inv_apply]
  congr 2; field_simp
end PositivityTheory.ThKG.Loc.Bump
