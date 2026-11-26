-- Prove2me | solution 1 for TDLC.step2PreservesParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:30.969052+00:00
-- url     : https://prove2.me/submissions/a99f4e90-c4d8-49c4-986d-4023644a6514


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_bxor_self
import Theorems.Thm_TDLC_bxor_comm
import Theorems.Thm_TDLC_Path_parity_lEmbed
import Theorems.Thm_TDLC_Path_parity_concat
import Theorems.Thm_TDLC_Path_parity_inv
import Theorems.Thm_TDLC_Path_parity_ap
attribute [local simp] TDLC.bxor_self
attribute [local simp] TDLC.Path.parity_lEmbed
attribute [local simp] TDLC.Path.parity_concat
attribute [local simp] TDLC.Path.parity_inv
attribute [local simp] TDLC.Path.parity_ap

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) : Path.parity p = Path.parity q := by
  induction cell with
  | cReflStep s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_lEmbed]
      change bxor false (Step.parity s) = bxor (Step.parity s) false
      exact bxor_comm _ _
  | betaStep f s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_ap]
      repeat rw [Path.parity_lEmbed]
      change bxor (Step.parity s) true = bxor true (Step.parity s)
      exact bxor_comm _ _
  | etaStep s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_ap]
      repeat rw [Path.parity_lEmbed]
      change bxor (Step.parity s) false = bxor false (Step.parity s)
      exact bxor_comm _ _
  | lamCongStep h s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_ap]
      repeat rw [Path.parity_lEmbed]
      change bxor (Step.parity s) false = bxor false (Step.parity s)
      exact bxor_comm _ _
  | refl2 p => rfl
  | sym2 cell ih => exact ih.symm
  | trans2 first second ihFirst ihSecond => exact ihFirst.trans ihSecond
  | reflStep2 x =>
      rw [Path.parity_lEmbed]
      rfl
  | symStep2 s =>
      rw [Path.parity_lEmbed, Path.parity_inv, Path.parity_lEmbed]
      rfl
  | transStep2 s t =>
      rw [Path.parity_lEmbed, Path.parity_concat,
        Path.parity_lEmbed, Path.parity_lEmbed]
      rfl
  | leftInvStep2 s =>
      rw [Path.parity_concat, Path.parity_inv, Path.parity_lEmbed]
      change bxor (Step.parity s) (Step.parity s) = false
      exact bxor_self _
  | rightInvStep2 s =>
      rw [Path.parity_concat, Path.parity_inv, Path.parity_lEmbed]
      change bxor (Step.parity s) (Step.parity s) = false
      exact bxor_self _
  | symSymStep2 s =>
      rw [Path.parity_lEmbed, Path.parity_lEmbed]
      rfl
  | apCongIdStep2 s =>
      rw [Path.parity_ap]
  | apCongStep2 f cell ih =>
      rw [Path.parity_ap, Path.parity_ap]
      exact ih
  | apCongComposeStep2 g f s =>
      rw [Path.parity_ap, Path.parity_ap, Path.parity_ap]
  | cong2 s cell ih =>
      change
        bxor (Step.parity s) (Path.parity _) =
          bxor (Step.parity s) (Path.parity _)
      exact congrArg (bxor (Step.parity s)) ih
  | whiskR2 cell r ih =>
      rw [Path.parity_concat, Path.parity_concat]
      exact congrArg (fun b => bxor b (Path.parity r)) ih
end TDLC
