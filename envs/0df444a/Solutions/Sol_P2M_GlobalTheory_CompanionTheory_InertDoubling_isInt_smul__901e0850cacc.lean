-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_smul__901e0850cacc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:32.832243+00:00
-- url     : https://prove2.me/submissions/a025573a-9f3e-4f1e-bcc2-dd417215cede

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertDoubling
theorem _root_.solution {m p : Type} {A : Matrix m p L} {c : L} (hc : c ∈ intL L) (h : IsInt A) : IsInt (c • A) :=
  fun i j => mul_mem hc (h i j)
end GlobalTheory.CompanionTheory.InertDoubling
