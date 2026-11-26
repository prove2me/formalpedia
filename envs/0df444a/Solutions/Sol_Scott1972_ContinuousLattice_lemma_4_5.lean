-- Prove2me | solution 1 for Scott1972.ContinuousLattice.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:17.322699+00:00
-- url     : https://prove2.me/submissions/222f39f1-cfdd-44fb-9cb9-e4703a4005cc

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_embInf_succ
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_con_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_min_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition314_fixMap_apply
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.con_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.min_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition314.fixMap_apply



set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (u : ∀ n, D (n + 1))
    (hu : ∀ n, (P (n + 1)).retr (u (n + 1)) = u n) (n : ℕ) :
    (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P).1 (n + 1) = u n := by
  let a : ℕ → InverseLimit D P := fun k => embInf D P (k + 1) (u k)
  have ha_succ (k : ℕ) : a k ≤ a (k + 1) := by
    rw [show a k = embInf D P (k + 1) (u k) from rfl,
      show a (k + 1) = embInf D P (k + 2) (u (k + 1)) from rfl,
      ← embInf_succ D P (k + 1) (u k)]
    exact embInf_monotone D P (k + 2)
      (by calc (P (k + 1)).incl (u k)
            = (P (k + 1)).incl ((P (k + 1)).retr (u (k + 1))) := by rw [hu k]
          _ ≤ u (k + 1) := (P (k + 1)).incl_retr_le _)
  have ha : Monotone a := monotone_nat_of_le_succ ha_succ
  have hprojLE : ∀ d n : ℕ,
      projLE D P (show n + 1 ≤ n + d + 1 by omega) (u (n + d)) = u n := by
    intro d
    induction d with
    | zero =>
        intro n
        simpa only [Nat.add_zero] using
          (projLE_self D P (le_refl (n + 1)) (u n))
    | succ d ih =>
        intro n
        simp only [Nat.add_succ]
        rw [projLE_succ D P
          (show n + 1 ≤ n + d + 1 by omega)
          (show n + 1 ≤ (n + d + 1) + 1 by omega)]
        rw [hu (n + d)]
        exact ih n
  have hprojection : ∀ d n : ℕ,
      (embInf D P (n + d + 1) (u (n + d))).1 (n + 1) = u n := by
    intro d n
    cases d with
    | zero =>
        change iComp D P (n + 1) (u n) (n + 1) = u n
        exact iComp_self D P (n + 1) (u n)
    | succ d =>
        change iComp D P (n + (d + 1) + 1) (u (n + (d + 1))) (n + 1) = u n
        rw [iComp_of_ge D P (by omega)]
        exact hprojLE (d + 1) n
  have hdir : DirectedOn (· ≤ ·) (Set.range a) :=
    directedOn_range.2 ha.directed_le
  have hcont := (projInf D P (n + 1)).preservesDirectedSup_coe
    (Set.range a) (Set.range_nonempty a) hdir
  rw [show (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P)
      = sSup (Set.range a) from sSup_range.symm]
  change (projInf D P (n + 1)) (sSup (Set.range a)) = u n
  rw [hcont, ← Set.range_comp, sSup_range]
  apply le_antisymm
  · exact iSup_le fun m => by
      by_cases hmn : n ≤ m
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact le_of_eq (hprojection d n)
      · exact le_trans ((ha (Nat.le_of_not_ge hmn)) (n + 1))
          (le_of_eq (hprojection 0 n))
  · exact le_trans (le_of_eq (hprojection 0 n).symm) (le_iSup (fun m => (a m).1 (n + 1)) n)
end Scott1972.ContinuousLattice
