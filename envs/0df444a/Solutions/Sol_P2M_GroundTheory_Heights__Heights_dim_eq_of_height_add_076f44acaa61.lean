-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_dim_eq_of_height_add_076f44acaa61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:49.139635+00:00
-- url     : https://prove2.me/submissions/7db936a6-e514-4c9d-be0e-cfbe313d319f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {h : ℕ∞} {x : WithBot ℕ∞} {e : ℕ} (h1 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (hh : h ≤ 1) (hsum : (h : WithBot ℕ∞) + x = ((e + 1 : ℕ) : WithBot ℕ∞)) : x = ((e : ℕ) : WithBot ℕ∞) := by
  cases x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hsum; exact absurd hsum (WithBot.bot_ne_natCast _)
  | coe y =>
    cases y using ENat.recTopCoe with
    | top =>
      have h1' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((e + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
      rw [WithBot.coe_le_coe, top_add, top_le_iff] at h1'
      exact absurd h1' (ENat.natCast_ne_top _)
    | coe y =>
      cases h using ENat.recTopCoe with
      | top => simp at hh
      | coe h =>
        have a1 : h + y = e + 1 := by exact_mod_cast hsum
        have a2 : h ≤ 1 := by exact_mod_cast hh
        have a3 : y + 1 ≤ e + 1 := by exact_mod_cast h1
        have : y = e := by omega
        subst this; rfl
end GroundTheory.Heights₂.Heights
