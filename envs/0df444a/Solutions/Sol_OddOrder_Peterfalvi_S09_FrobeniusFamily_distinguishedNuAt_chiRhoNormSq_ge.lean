-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.distinguishedNuAt_chiRhoNormSq_ge
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:35:18.240742+00:00
-- url     : https://prove2.me/submissions/eeccac2d-070b-4243-9bdb-1d0d5297fae5

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean
--   OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis78
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_zetaNuRhoNormSq_ge_at

-- ===== OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09.Cert

/-- **The `ρ`-map is restriction, for a TI Dade datum** (trivial local subgroups `H(a) = ⊥`, the
`of_isTISubset` case).  For `a ∈ A`, the `(7.2)` coset average
`χ^ρ(a) = (1/|H(a)|) ∑_{x ∈ H(a)} χ(a·x)` collapses (each `x = 1`, so every summand is `χ(a)`) to
`χ(a)`.  This is what makes two `Hypothesis71`'s built from the *same* TI subset — even via
different
`of_isTISubset` expressions — agree on `chiRho` (hence `chiRhoCF`/`chiRhoNormSq`). -/
theorem chiRho_apply_of_trivial_local {G : Type*} [Group G] {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card G : ℂ)] (H71 : Hypothesis71 G A L)
    (hbot : ∀ (a : G) (ha : a ∈ A), H71.hyp.H ⟨a, ha⟩ = ⊥)
    (χ : ClassFunction G ℂ) {a : L} (ha : (a : G) ∈ A) :
    H71.chiRho χ a = χ (a : G) := by
  classical
  rw [H71.chiRho_of_mem χ ha]
  have hval : ∀ x : ↥(H71.hyp.H ⟨(a : G), ha⟩), χ ((a : G) * (x : G)) = χ (a : G) := by
    intro x
    have hx2 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hbot (a : G) ha]; exact x.2
    rw [Subgroup.mem_bot.mp hx2, mul_one]
  have hne : (Nat.card (H71.hyp.H ⟨(a : G), ha⟩) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos).ne'
  rw [Finset.sum_congr rfl (fun x _ => hval x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley (7.1) `ρ`-map equals the family (7.1) `ρ`-map** (the (7.8.b)→(7.5) bridge).  Both
`sibleyToHypothesis71 i` (the Dade datum coherence is coherent for) and `hypothesis71 i` (the family
`FamilyHypothesis71` uses) are `of_isTISubset` on the *same* TI subset `H_i^#` (their supports agree
by `sharpImage_subgroupOf_eq`), with trivial local subgroups, so `chiRho` (hence `chiRhoCF`) is
restriction to `H_i^#` for both — they coincide (`chiRho_apply_of_trivial_local`).  This identifies
`H78.zetaNuRhoNormSq` (built on `sibleyToHypothesis71`) with `P.chiRhoNormSq` (built on
`hypothesis71`), the last link from the (7.8.b) bound to the (7.5) family estimate. -/
theorem sibleyToHypothesis71_chiRhoCF_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    (χ : ClassFunction G ℂ) :
    (F.sibleyToHypothesis71 i hodd hnilp C hFrob).chiRhoCF χ = (F.hypothesis71 i).chiRhoCF χ := by
  ext a
  rw [Hypothesis71.chiRhoCF_apply, Hypothesis71.chiRhoCF_apply]
  by_cases ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)
  · have haS : (a : G) ∈ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact ha
    rw [chiRho_apply_of_trivial_local _ (fun _ _ => rfl) χ haS,
      chiRho_apply_of_trivial_local _ (fun _ _ => rfl) χ ha]
  · have haS : (a : G) ∉ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact ha
    rw [(F.sibleyToHypothesis71 i hodd hnilp C hFrob).chiRho_of_not_mem χ haS,
      (F.hypothesis71 i).chiRho_of_not_mem χ ha]

end FrobeniusFamily

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilySelectedEstimate

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- **Peterfalvi (7.8.b), family consumer form.**  The canonical character
used to define the reverse-coefficient set in (7.10) satisfies the selected
member's rho-norm lower bound. -/
theorem _root_.solution (i : Fin k) :
    (1 : ℝ) - (F.e i : ℝ) / (F.h i : ℝ) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) i := by
  classical
  let : Fintype ↥(F.L i) := (F.familyHypothesis71).fintypeL i
  let : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    (F.familyHypothesis71).invertibleL i
  let : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  let H78 := F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)
  have hbound := F.hypothesis78_zetaNuRhoNormSq_ge_at
    i hodd (hnilp i) (C i) (hFrob i)
  have he : H78.complementIndex = F.e i := rfl
  have hh : H78.kernelOrder = F.h i := rfl
  have hnorm : H78.zetaNuRhoNormSq =
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) i := by
    change (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re = _
    have hcf : H78.zetaNuRho =
        (F.hypothesis71 i).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i) := by
      change (F.sibleyToHypothesis71 i hodd (hnilp i) (C i) (hFrob i)).chiRhoCF
          (H78.nu (H78.hyp76.zeta 0)) =
        (F.hypothesis71 i).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i)
      rw [F.sibleyToHypothesis71_chiRhoCF_eq]
      rfl
    rw [hcf]
    rfl
  rw [he, hh, hnorm] at hbound
  exact hbound

end FamilySelectedEstimate

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
