-- Prove2me | solution 1 for Trace.traceEquiv_imp_labelEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:56.202808+00:00
-- url     : https://prove2.me/submissions/eb1d5039-9310-415b-a58b-74ed207d31c2

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Theorems.Thm_Trace_labels_swap_iff
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open Trace
namespace Trace
theorem _root_.solution (hresp : LabelRespecting R lbl)
    {t₁ t₂ : List α} (h : TraceEquiv R t₁ t₂) : LabelEquiv lbl t₁ t₂ := by
  induction h with
  | refl _ => rfl
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    have hlab : lbl e₁ = lbl e₂ := hresp ind
    have hsame : labels lbl (t₁' ++ e₂ :: e₁ :: t₂') = labels lbl (t₁' ++ e₁ :: e₂ :: t₂') :=
      (labels_swap_iff lbl).mpr hlab.symm
    exact hsame.trans ih
end Trace
