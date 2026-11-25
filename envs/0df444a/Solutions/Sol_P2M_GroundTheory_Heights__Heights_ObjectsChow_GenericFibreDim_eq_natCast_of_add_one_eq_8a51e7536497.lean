-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_eq_natCast_of_add_one_eq_8a51e7536497
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:58.591567+00:00
-- url     : https://prove2.me/submissions/5486548b-1dde-4ae0-8c33-58633268d304

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
namespace GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
theorem _root_.solution (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
