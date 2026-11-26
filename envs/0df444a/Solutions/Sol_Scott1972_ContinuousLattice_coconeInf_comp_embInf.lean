-- Prove2me | solution 1 for Scott1972.ContinuousLattice.coconeInf_comp_embInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:18.325008+00:00
-- url     : https://prove2.me/submissions/29d386bc-dd77-41f9-8f33-018250102a96

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_climb
import Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_descend
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) (n : ℕ) (x : D n) :
    coconeInf D P f (embInf D P n x) = f n x := by
  apply le_antisymm
  · show (⨆ m, f m ((embInf D P n x).1 m)) ≤ f n x
    refine iSup_le fun m => ?_
    show f m (iComp D P n x m) ≤ f n x
    by_cases h : n ≤ m
    · rw [iComp_of_le D P h]; exact le_of_eq (coconeInf_climb D P f hf x h)
    · rw [iComp_of_ge D P h]; exact coconeInf_descend D P f hf (le_of_lt (not_le.mp h)) x
  · refine le_trans (le_of_eq ?_) (le_iSup (fun m => f m ((embInf D P n x).1 m)) n)
    rw [show (embInf D P n x).1 n = x from iComp_self D P n x]
end Scott1972.ContinuousLattice
