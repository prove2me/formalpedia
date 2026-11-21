-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSeminorm_neg
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:05:15.954178+00:00
-- url     : https://prove2.me/submissions/b16f4775-967c-4535-a458-9c8aa8e33bf1

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L403-L406
import Theorems.Thm_RiemannMasullo_elementarySchwartzSeminorm_smul
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
theorem solution (i : ElementarySchwartzIndex m n r)
    (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (-f).val i).toReal =
      (elementarySchwartzBound f.val i).toReal := by
  simpa using elementarySchwartzSeminorm_smul i (-1 : ℂ) f
