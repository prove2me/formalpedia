-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_weightedNuSum_inner_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:22:55.163713+00:00
-- url     : https://prove2.me/submissions/f60f51c2-97d2-4ad6-8079-b337103d756e

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex

-- ===== OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section WeightedNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

/-- The squared norm of the weighted coherent sum is the local ratio
(h_i - 1) / e_i. -/
theorem _root_.solution :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum =
        (((((F.h i : ℝ) - 1) / (F.e i : ℝ)) : ℝ) : ℂ) := by
  classical
  let H78 := F.hypothesis78 i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  change ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
    (((((F.h i : ℝ) - 1) / (F.e i : ℝ)) : ℝ) : ℂ)
  have hzeta :
      H78.hyp76.zeta =
        fun r => ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ r : ClassFunction _ ℂ) :=
    F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob
  have horth_if : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta s) =
          if r = s then
            ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)
          else 0 := by
    intro r _ s _
    by_cases hrs : r = s
    · rw [if_pos hrs, hrs]
    · rw [if_neg hrs, congrFun hzeta r, congrFun hzeta s]
      exact Cert.induce_family_orthogonal_of_injective
        ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj r s hrs
  have hnorm_ne : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r) ≠ 0 := by
    intro r _
    rw [congrFun hzeta r]
    exact Cert.induce_norm_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ r)
  have hzeta_degree :
      H78.hyp76.zeta H78.zetaDistinct (1 : ↥(F.L i)) =
        (H78.complementIndex : ℂ) := by
    rw [show H78.zetaDistinct = 0 from rfl, congrFun hzeta 0,
      Cert.complementIndex_eq_subgroupOf_index H78]
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ)
    rw [pf.induce_zero_eq]
    exact
      (Classical.choose_spec
        (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  have hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : ↥(F.L i)) *
            star (H78.hyp76.zeta r (1 : ↥(F.L i))) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) := by
    have hstar : ∀ r : Fin (H78.hyp76.n + 1),
        star (H78.hyp76.zeta r (1 : ↥(F.L i))) =
          H78.hyp76.zeta r (1 : ↥(F.L i)) := by
      intro r
      rw [congrFun hzeta r]
      exact Cert.induce_apply_one_star
        ((F.H i).subgroupOf (F.L i)) (pf.θ r)
    have hsq : ∀ r : Fin (H78.hyp76.n + 1),
        H78.hyp76.zeta r (1 : ↥(F.L i)) *
            star (H78.hyp76.zeta r (1 : ↥(F.L i))) =
          H78.hyp76.zeta r (1 : ↥(F.L i)) ^ 2 := by
      intro r
      rw [hstar r, sq]
    have hind : H78.ind1H = pf.ind1H := rfl
    calc
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
          H78.hyp76.zeta r (1 : ↥(F.L i)) *
              star (H78.hyp76.zeta r (1 : ↥(F.L i))) /
            ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ∑ r ∈ (Finset.univ.erase H78.ind1H),
          H78.hyp76.zeta r (1 : ↥(F.L i)) ^ 2 /
            ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r) :=
        Finset.sum_congr rfl fun r _ => by rw [hsq r]
      _ = (((F.H i).subgroupOf (F.L i)).index : ℂ) *
          ((Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) - 1) := by
        change
          (∑ r ∈ (Finset.univ.erase pf.ind1H),
            ClassFunction.induce ((F.H i).subgroupOf (F.L i))
                (pf.θ r : ClassFunction _ ℂ) (1 : ↥(F.L i)) ^ 2 /
              ClassFunction.inner
                (ClassFunction.induce ((F.H i).subgroupOf (F.L i))
                  (pf.θ r : ClassFunction _ ℂ))
                (ClassFunction.induce ((F.H i).subgroupOf (F.L i))
                  (pf.θ r : ClassFunction _ ℂ))) =
            (((F.H i).subgroupOf (F.L i)).index : ℂ) *
              ((Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) - 1)
        exact Cert.family_degree_sum ((F.H i).subgroupOf (F.L i))
          pf.θ pf.inj pf.cover pf.ind1H pf.triv
      _ = ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) := by
        have hke :
            (H78.kernelOrder : ℂ) =
              (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) := by
          exact_mod_cast
            (Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv).symm
        have hce :
            (H78.complementIndex : ℂ) =
              (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
          exact_mod_cast Cert.complementIndex_eq_subgroupOf_index H78
        rw [hke, hce]
        ring
  have hnorm :=
    H78.weightedNuSum_inner_self_eq_of_source_orthogonal
      horth_if hnorm_ne hzeta_degree hdegree_sum
  have hh : H78.kernelOrder = F.h i := rfl
  have he : H78.complementIndex = F.e i := rfl
  rw [hh, he] at hnorm
  convert hnorm using 1
  all_goals norm_num

end WeightedNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
