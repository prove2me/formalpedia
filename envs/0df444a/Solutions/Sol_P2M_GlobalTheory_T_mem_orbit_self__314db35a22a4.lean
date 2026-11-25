-- Prove2me | solution 1 for P2M_GlobalTheory_T_mem_orbit_self__314db35a22a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:09:40.560921+00:00
-- url     : https://prove2.me/submissions/a0a303ec-d535-4618-8c01-0931bb11a4ae

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_MemOrbitSelf
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_MemOrbitSelfStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_mem_orbit_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left), x ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | exact GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self <;> assumption)
end _root_.GlobalTheory.T
