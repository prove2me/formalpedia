-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_zeta_ne_conj
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:23:08.758242+00:00
-- url     : https://prove2.me/submissions/85139e43-6982-46db-ab1c-bbca6e8589ac

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusEstimate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex

-- ===== OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The distinguished `ζ` is not real** (odd order): `ζ ≠ ζ̄`.  It is a nontrivial irreducible
character (degree `[L:K] > 1`) of the odd-order group `L`, so by (1.1) it is not real.  Supplies
`hζ₁ne_conj`/`hζ₂ne_conj` to `zetaImage_cross_eq_zero_of_conjIndex`. -/
theorem _root_.solution [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
      ≠ ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hirr := F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob
  -- `L` has odd order (subgroup of the odd `G`).
  have hodd_L : Odd (Nat.card ↥(F.L i)) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- The kernel is proper (complement nontrivial), so `[L:K] > 1`.
  have hK_ne_top : (F.H i).subgroupOf (F.L i) ≠ ⊤ := by
    intro hKtop
    refine hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := hFrob.isComplement.disjoint
    rw [hKtop] at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < ((F.H i).subgroupOf (F.L i)).index :=
    Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_0 (1) = [L:K] ≠ 1`, so `ζ_0 ≠ 1_L`.
  have hdeg : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct (1 : ↥(F.L i))
      = (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
    have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
    have hz0χ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0
        = Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob) := by
      rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
      exact (F.sibleyPlacedFamily i hodd hnilp C hFrob).induce_zero_eq
    rw [hzd, hz0χ]
    exact (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  have hne_triv : (⟨(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct, hirr⟩ : IrreducibleCharacter ↥(F.L i))
      ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = trivialClassFunction ↥(F.L i) := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((F.H i).subgroupOf (F.L i)).index : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    exact absurd (by exact_mod_cast hone : ((F.H i).subgroupOf (F.L i)).index = 1) (by omega)
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
