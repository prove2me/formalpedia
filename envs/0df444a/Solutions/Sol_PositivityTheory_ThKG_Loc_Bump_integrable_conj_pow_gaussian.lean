-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.integrable_conj_pow_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:24.506054+00:00
-- url     : https://prove2.me/submissions/3e08f9ba-763d-4c75-9a10-3fc9814192ae

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_gauss
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_int_pg

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
theorem _root_.solution (k : ℕ) : Integrable fun z : ℂ => conj z ^ k * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2) :=
  int_pg (by fun_prop) k fun z => by rw [norm_mul, norm_gauss, norm_pow, Complex.norm_conj]
end PositivityTheory.ThKG.Loc.Bump
