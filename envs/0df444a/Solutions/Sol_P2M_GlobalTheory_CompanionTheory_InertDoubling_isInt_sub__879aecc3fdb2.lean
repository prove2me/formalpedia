-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_sub__879aecc3fdb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:13.560703+00:00
-- url     : https://prove2.me/submissions/fa587505-ead1-493a-aa42-7e5cceb44283

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
theorem _root_.solution {m p : Type} {A B : Matrix m p L} (h : IsInt A) (h' : IsInt B) : IsInt (A - B) :=
  fun i j => sub_mem (h i j) (h' i j)
end GlobalTheory.CompanionTheory.InertDoubling
