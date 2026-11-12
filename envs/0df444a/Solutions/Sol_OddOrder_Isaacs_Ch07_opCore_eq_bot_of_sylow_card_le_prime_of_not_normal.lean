-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:32.458467+00:00
-- url     : https://prove2.me/submissions/207df696-a73b-4c3e-acd9-063d128e9181

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- If a Sylow `p`-subgroup has order at most `p` and is not normal, then `O_p(G)=1`.

This is the `O_p(G)=1` reduction in Isaacs Thm 7.5 after the faithful action has embedded
the group into `GL(2,p)` and `gl2_pSubgroup_card_le_prime` has bounded `|P|`. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP_card : Nat.card (P : Subgroup G) ≤ p)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) :
    OddOrder.Isaacs.Ch01.opCore p G = ⊥ := by
  by_contra hOp_ne_bot
  have hOp_le_P : OddOrder.Isaacs.Ch01.opCore p G ≤ (P : Subgroup G) :=
    OddOrder.Isaacs.Ch01.opCore_le P
  have hOp_p : IsPGroup p (OddOrder.Isaacs.Ch01.opCore p G) :=
    OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hOp_p
  have hOp_gt_one : 1 < Nat.card (OddOrder.Isaacs.Ch01.opCore p G) :=
    (Subgroup.one_lt_card_iff_ne_bot (OddOrder.Isaacs.Ch01.opCore p G)).mpr hOp_ne_bot
  have hp_le_Op : p ≤ Nat.card (OddOrder.Isaacs.Ch01.opCore p G) := by
    cases n with
    | zero =>
        have hcard_one : Nat.card (OddOrder.Isaacs.Ch01.opCore p G) = 1 := by
          simpa using hn
        omega
    | succ n =>
        rw [hn, pow_succ]
        have hpow_pos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
        simpa [mul_comm] using Nat.le_mul_of_pos_right p hpow_pos
  have hOp_card_le_P : Nat.card (OddOrder.Isaacs.Ch01.opCore p G) ≤
      Nat.card (P : Subgroup G) :=
    Subgroup.card_le_of_le hOp_le_P
  have hP_card_eq : Nat.card (P : Subgroup G) = p :=
    le_antisymm hP_card (hp_le_Op.trans hOp_card_le_P)
  have hOp_card_eq : Nat.card (OddOrder.Isaacs.Ch01.opCore p G) = p :=
    le_antisymm (hOp_card_le_P.trans hP_card) hp_le_Op
  have hOp_eq_P : OddOrder.Isaacs.Ch01.opCore p G = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hOp_le_P (by rw [hP_card_eq, hOp_card_eq])
  apply hP_not_normal
  rw [← hOp_eq_P]
  infer_instance

end OddOrder.Isaacs.Ch07
