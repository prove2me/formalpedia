-- Prove2me | solution 1 for ShockCBM.ControlLimit.rhs19_monotone_x
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:21:29.136431+00:00
-- url     : https://prove2.me/submissions/c618ef21-6e44-445c-8377-806f3b14f432

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting
import Theorems.Thm_ShockCBM_ControlLimit_Enext_monotone_x
import Theorems.Thm_ShockCBM_ControlLimit_lemma_2_ii
import Theorems.Thm_ShockCBM_ControlLimit_display_10

open ShockCBM.ControlLimit

theorem solution (M : Model) (hM : M.Standing) (x x' n t : ℕ) (hxx : x ≤ x') :
    M.Enext (x, n, t) M.V ≤ M.Enext (x', n, t) M.V :=
  Enext_monotone_x M hM M.V (M.cu / (1 - M.γ)) (fun s => ((display_10 M hM).2.2 s).1)
    (fun s => ((display_10 M hM).2.2 s).2) (fun x x' n t h => lemma_2_ii M hM x x' n t h) x x' n t hxx
