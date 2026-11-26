-- Prove2me | solution 1 for TDLC.Refutation.cell_preserves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:02.936373+00:00
-- url     : https://prove2.me/submissions/5f6445ca-c79c-44d5-8059-90c9a27ccc10

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Refutation
import Theorems.Thm_TDLC_Refutation_endpoints
import Theorems.Thm_TDLC_Refutation_grade_constant
import Theorems.Thm_TDLC_Refutation_pathGrade_embed
import Theorems.Thm_TDLC_Refutation_pathGrade_concat
import Theorems.Thm_TDLC_Refutation_pathGrade_ap
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
theorem _root_.solution {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by
  classical
  induction cell with
  | cReflStep s =>
      simp only [pathGrade_concat, pathGrade_embed, grade, g.one_mul, g.mul_one]
  | betaStep f s =>
      have he := endpoints s
      cases he
      simp only [pathGrade_concat, pathGrade_ap, pathGrade_embed, grade]
      split
      next hc =>
        rename_i a
        have constant : Constant f := of_decide_eq_true hc
        have hg := grade_constant g mark s (fun x => val (f x)) (val (f a))
          (fun x => congrArg val (constant x a))
        rw [hg, g.one_mul, g.mul_one]
      next => simp only [g.one_mul, g.mul_one]
  | etaStep s =>
      simp only [pathGrade_concat, pathGrade_ap, Path.lEmbed, pathGrade, grade, etaExpand,
        g.one_mul, g.mul_one]
      rfl
  | lamCongStep h s =>
      have he := endpoints (Step.lamCong h)
      cases he
      simp only [pathGrade_concat, pathGrade_ap, pathGrade_embed, grade,
        g.one_mul, g.mul_one]
  | refl2 => rfl
  | sym2 c ih => exact (ih val).symm
  | trans2 c d ihc ihd => exact (ihc val).trans (ihd val)
  | reflStep2 => exact g.mul_one _
  | symStep2 s => simp only [Path.inv, Path.lEmbed, Path.concat, pathGrade, grade]
  | transStep2 s t =>
      simp only [pathGrade_embed, pathGrade_concat, grade]
  | leftInvStep2 s =>
      simp only [Path.inv, Path.lEmbed, Path.concat, pathGrade, grade,
        g.mul_one, g.inv_mul]
  | rightInvStep2 s =>
      simp only [Path.inv, Path.lEmbed, Path.concat, pathGrade, grade,
        g.mul_one, g.mul_inv]
  | symSymStep2 s => simp only [pathGrade_embed, grade, g.inv_inv]
  | apCongIdStep2 s => simp only [pathGrade_ap]
  | apCongStep2 f c ih => simpa only [pathGrade_ap] using ih (fun x => val (f x))
  | apCongComposeStep2 f h s => simp only [pathGrade_ap]
  | cong2 s c ih => simp only [pathGrade, ih]
  | whiskR2 c r ih => simp only [pathGrade_concat, ih]
end TDLC.Refutation
