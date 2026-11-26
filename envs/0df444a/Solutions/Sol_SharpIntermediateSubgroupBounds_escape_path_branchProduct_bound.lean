-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escape_path_branchProduct_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:24.450381+00:00
-- url     : https://prove2.me/submissions/c19810a5-37ed-433c-96a2-cb6d3868b2ff

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeChoice_card_of_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeChoice_ratio_of_ne
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_nonneg
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero


attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    {s : EscapeState K} (hHs : H ≤ s.1) (z : EscapePath K r s) :
    gammaQ H.index.minFac (escapeStrictCount K z) *
        (Nat.card K : ℚ) ^ r ≤
      (BranchingTree.branchProduct (EscapeChoice K) (escapeNext K) z : ℚ) := by
  have hp : 1 < H.index.minFac :=
    (Nat.minFac_prime (by omega : H.index ≠ 1)).one_lt
  induction r generalizing s with
  | zero =>
      simp [escapeStrictCount, BranchingTree.branchProduct]
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change gammaQ H.index.minFac
          (escapeStrictCount K (escapeCons K x z)) *
            (Nat.card K : ℚ) ^ (r + 1) ≤
        (BranchingTree.branchProduct (EscapeChoice K) (escapeNext K)
          (escapeCons K x z) : ℚ)
      have hHnext : H ≤ (escapeNext K s x).1 := hHs.trans le_sup_left
      have htail := ih hHnext z
      by_cases hs : s.1 = K
      · have hcard : Fintype.card (EscapeChoice K s) = Nat.card K :=
          escapeChoice_card_of_eq K s hs
        rw [escapeStrictCount_cons, if_pos hs,
          pow_succ (Nat.card K : ℚ) r]
        calc
          gammaQ H.index.minFac (escapeStrictCount K z) *
                ((Nat.card K : ℚ) ^ r * Nat.card K) =
              (Nat.card K : ℚ) *
                (gammaQ H.index.minFac (escapeStrictCount K z) *
                  (Nat.card K : ℚ) ^ r) := by ring
          _ ≤ (Nat.card K : ℚ) *
                (BranchingTree.branchProduct (EscapeChoice K)
                  (escapeNext K) z : ℚ) :=
              mul_le_mul_of_nonneg_left htail (by positivity)
          _ = (BranchingTree.branchProduct (EscapeChoice K) (escapeNext K)
                (escapeCons K x z) : ℚ) := by
              simp only [escapeBranchProduct_cons, Nat.cast_mul, hcard]
      · have hchain := escape_chain_bound hHK hHs (escapeCons K x z)
        rw [escapeStrictCount_cons, if_neg hs] at hchain
        have hendPos : 0 < (escapeEnd K z).1.relIndex K := by
          letI : (escapeEnd K z).1.IsFiniteRelIndex K :=
            (escapeEnd K z).1.isFiniteRelIndex_of_finiteIndex
          exact Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
        have hpowLe : H.index.minFac ^ (escapeStrictCount K z + 1) ≤
            s.1.relIndex K := by
          apply le_trans (Nat.le_mul_of_pos_right _ hendPos)
          simpa only [escapeEnd_cons] using hchain
        have hpowPos : 0 < H.index.minFac ^ (escapeStrictCount K z + 1) :=
          pow_pos (by omega) _
        have hpowPosQ : (0 : ℚ) <
            (H.index.minFac : ℚ) ^ (escapeStrictCount K z + 1) := by
          exact_mod_cast hpowPos
        have hpowLeQ :
            (H.index.minFac : ℚ) ^ (escapeStrictCount K z + 1) ≤
              (s.1.relIndex K : ℚ) := by
          exact_mod_cast hpowLe
        have hinv :
            1 / (s.1.relIndex K : ℚ) ≤
              1 / (H.index.minFac : ℚ) ^ (escapeStrictCount K z + 1) := by
          exact one_div_le_one_div_of_le hpowPosQ hpowLeQ
        have hnormalized :
            1 - 1 / (H.index.minFac : ℚ) ^ (escapeStrictCount K z + 1) ≤
              (Fintype.card (EscapeChoice K s) : ℚ) / Nat.card K := by
          rw [escapeChoice_ratio_of_ne K s hs]
          exact sub_le_sub_left hinv 1
        have hkPos : (0 : ℚ) < (Nat.card K : ℚ) :=
          Nat.cast_pos.mpr Nat.card_pos
        have hfactor :
            (1 - 1 / (H.index.minFac : ℚ) ^
                (escapeStrictCount K z + 1)) * (Nat.card K : ℚ) ≤
              Fintype.card (EscapeChoice K s) :=
          (le_div_iff₀ hkPos).mp hnormalized
        rw [escapeStrictCount_cons, if_neg hs, gammaQ_succ,
          pow_succ (Nat.card K : ℚ) r]
        · calc
            (gammaQ H.index.minFac (escapeStrictCount K z) *
                  (1 - 1 / (H.index.minFac : ℚ) ^
                    (escapeStrictCount K z + 1))) *
                  ((Nat.card K : ℚ) ^ r * Nat.card K) =
                ((1 - 1 / (H.index.minFac : ℚ) ^
                    (escapeStrictCount K z + 1)) * Nat.card K) *
                  (gammaQ H.index.minFac (escapeStrictCount K z) *
                    (Nat.card K : ℚ) ^ r) := by ring
            _ ≤ (Fintype.card (EscapeChoice K s) : ℚ) *
                  (gammaQ H.index.minFac (escapeStrictCount K z) *
                    (Nat.card K : ℚ) ^ r) :=
                mul_le_mul_of_nonneg_right hfactor
                  (mul_nonneg (gammaQ_nonneg hp) (by positivity))
            _ ≤ (Fintype.card (EscapeChoice K s) : ℚ) *
                  (BranchingTree.branchProduct (EscapeChoice K)
                    (escapeNext K) z : ℚ) :=
                mul_le_mul_of_nonneg_left htail (by positivity)
            _ = (BranchingTree.branchProduct (EscapeChoice K) (escapeNext K)
                  (escapeCons K x z) : ℚ) := by
                simp only [escapeBranchProduct_cons, Nat.cast_mul]
        · omega
end SharpIntermediateSubgroupBounds
