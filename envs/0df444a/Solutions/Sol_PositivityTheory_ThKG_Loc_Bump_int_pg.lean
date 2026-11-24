-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.int_pg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:44.487414+00:00
-- url     : https://prove2.me/submissions/4501d2b2-3234-4367-a4a1-5c3bf7dc5891

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_poly_le
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_int_of_le

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
theorem _root_.solution {g : ℂ → ℂ} (hg : Measurable g) (s : ℕ) (h : ∀ z, ‖g z‖ ≤ ‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2)) : Integrable g := by
  refine int_of_le hg (Real.exp ((s + 3 : ℕ) ^ 2)) fun z _ => le_trans ?_ (poly_le ‖z‖ (norm_nonneg z) (s + 3))
  have : ‖z‖ ^ s ≤ (1 + ‖z‖) ^ s := pow_le_pow_left₀ (norm_nonneg z) (by linarith) s
  calc _ ≤ (1 + ‖z‖) ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (1 + ‖z‖) ^ 3 := by
        gcongr; exact (h z).trans (by gcongr)
    _ = _ := by ring
end PositivityTheory.ThKG.Loc.Bump
