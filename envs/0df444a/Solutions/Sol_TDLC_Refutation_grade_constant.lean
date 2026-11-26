-- Prove2me | solution 1 for TDLC.Refutation.grade_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:31.427266+00:00
-- url     : https://prove2.me/submissions/6bae61db-35c3-43f9-a712-e13cdbbb5b04

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Path_parity_ap
import Theorems.Thm_TDLC_Path_parity_concat
import Theorems.Thm_TDLC_Path_parity_inv
import Theorems.Thm_TDLC_Path_parity_lEmbed
import Theorems.Thm_TDLC_bxor_false_left
import Theorems.Thm_TDLC_bxor_false_right
import Theorems.Thm_TDLC_bxor_self
attribute [local simp] TDLC.Path.parity_ap
attribute [local simp] TDLC.Path.parity_concat
attribute [local simp] TDLC.Path.parity_inv
attribute [local simp] TDLC.Path.parity_lEmbed
attribute [local simp] TDLC.bxor_false_left
attribute [local simp] TDLC.bxor_false_right
attribute [local simp] TDLC.bxor_self



set_option autoImplicit true
open TDLC TDLC.Refutation
universe u v
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
namespace TDLC.Refutation
theorem _root_.solution {A : Type u} {x y : A} (s : Step x y)
    (val : A → G) (c : G) (hc : ∀ x, val x = c) : grade g mark s val = g.one := by
  induction s with
  | beta f a =>
      simp only [grade]
      split <;> simp only [hc, g.inv_mul]
  | eta => rfl
  | apCong f s ih => exact ih (fun x => val (f x)) (fun x => hc (f x))
  | lamCong => rfl
  | refl => rfl
  | sym s ih => simp only [grade, ih val hc, g.inv_one]
  | trans s t ihs iht => simp only [grade, ihs val hc, iht val hc, g.one_mul]
end TDLC.Refutation
