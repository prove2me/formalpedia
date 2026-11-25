-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.integrable_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:56.36229+00:00
-- url     : https://prove2.me/submissions/ae943dfe-029f-4d70-ae8d-02dc960bcc8c

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_conj_pow_gaussian

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
theorem _root_.solution (κ : ι → ℕ) : Integrable (gm κ) := by
  have := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) fun w => integrable_conj_pow_gaussian (κ w)
  exact this
end PositivityTheory.ThKG.Loc.Bump
