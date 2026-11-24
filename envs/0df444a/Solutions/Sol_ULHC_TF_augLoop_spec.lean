-- Prove2me | solution 1 for ULHC.TF.augLoop_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:56:59.415971+00:00
-- url     : https://prove2.me/submissions/35abcfc3-abaf-4701-b960-8abd8d86f55d

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_augStep_some
import Theorems.Thm_ULHC_TF_card_le_of_good
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} :
    ∀ n F, Good V F → V.card < F.card + n →
      Good V (augLoop V n F) ∧ augStep V (augLoop V n F) = none := by
  intro n
  induction n with
  | zero =>
    intro F hF hn
    have := card_le_of_good hF
    omega
  | succ n ih =>
    intro F hF hn
    rcases h : augStep V F with _ | F'
    · simp only [augLoop, h, and_true]
      exact hF
    · simp only [augLoop, h]
      obtain ⟨hF', hc⟩ := augStep_some hF h
      exact ih F' hF' (by omega)
end ULHC.TF
