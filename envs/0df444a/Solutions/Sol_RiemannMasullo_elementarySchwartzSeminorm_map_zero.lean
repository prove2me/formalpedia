-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSeminorm_map_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:04:08.132687+00:00
-- url     : https://prove2.me/submissions/74aee712-1657-4a8f-b1e7-37329835de3b

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L382-L384
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
theorem solution (i : ElementarySchwartzIndex m n r) :
    (elementarySchwartzBound (0 : elementarySchwartzSubmodule m n r F).val i).toReal = 0 :=
  by
  change (elementarySchwartzBound (0 : ElementaryLieGroup m n r F → ℂ) i).toReal = 0
  simp [elementarySchwartzBound, elementaryPartial, iteratedFDeriv_fun_zero]
