-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_iff_forall_cartAt_7444c988f6eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:32.265298+00:00
-- url     : https://prove2.me/submissions/c5cbaff6-bcd0-4512-8141-44aabab4b891

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {X : Scheme.{0}} (J : X.IdealSheafData) :
    FinalTheorems.EffCartier J ↔ ∀ x, CartAt J x := Iff.rfl
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
