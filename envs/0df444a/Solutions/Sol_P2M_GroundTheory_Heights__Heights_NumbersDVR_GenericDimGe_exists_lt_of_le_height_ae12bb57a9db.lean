-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_lt_of_le_height_ae12bb57a9db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:30.056176+00:00
-- url     : https://prove2.me/submissions/7fa22eb6-a859-48ae-b741-ba8311de5e02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
theorem _root_.solution {α : Type*} [Preorder α] {a : α} {n : ℕ}
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ Order.height a) : ∃ b < a, (n : ℕ∞) ≤ Order.height b := by
  obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height a h
  have hne : p.length ≠ 0 := by omega
  refine ⟨p.eraseLast.last, hlast ▸ p.eraseLast_last_rel_last hne, ?_⟩
  have := Order.length_le_height_last (p := p.eraseLast)
  simp only [RelSeries.eraseLast_length, hlen, Nat.add_sub_cancel] at this
  exact this
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
