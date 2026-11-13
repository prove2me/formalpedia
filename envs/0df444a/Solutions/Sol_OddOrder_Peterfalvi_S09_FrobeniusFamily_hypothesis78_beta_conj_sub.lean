-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_beta_conj_sub
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:25:45.697451+00:00
-- url     : https://prove2.me/submissions/6a988910-a882-49c1-92c3-a6d67ae71bbc

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
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_exists_conjIndex_hypothesis78

-- ===== OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **`ζ − ζ̄` is supported on `A = H^#`** (equal degree).  Both `ζ = ζ_0` and `ζ̄ = ζ_{j₁}` are
induced from `K`, so vanish off `H`, and their common degree `ζ(1) = [L:K]` (real) makes the
difference vanish at `1`.  The `A`-support input to `coherence_hagree_dadeMap` for `hab_supp`. -/
theorem hypothesis78_zeta_sub_conj_support [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    {j₁ : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hj₁ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj) :
    ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
        - (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
  classical
  -- `ζ(1) = [L:K]` (as in `hypothesis78_zeta_ne_conj`).
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
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hj₁, ClassFunction.conj_apply] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, F.sharpImage_subgroupOf_eq i,
    OddOrder.Peterfalvi.S04.mem_sharp]
  refine ⟨?_, ?_⟩
  · -- `(x:G) ∈ H_i`: else `ζ x = 0`, so the difference vanishes.
    by_contra hxH
    apply hx
    rw [(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH,
      star_zero, sub_zero]
  · -- `(x:G) ≠ 1`: at `1`, `ζ(1) = [L:K]` is real, so `ζ(1) − star ζ(1) = 0`.
    intro hx1
    apply hx
    rw [OneMemClass.coe_eq_one.mp hx1, hdeg]
    simp

open OddOrder.Peterfalvi.S09.Cert in
/-- **`β̄ − β = νζ − νζ̄`** (Frobenius; the `hbeta_conj_sub` input to `delta_isReal`).
`β = τ⟨ζ_ind − ζ⟩`
with `ζ_ind = Ind 1_K` real; conjugating (`dadeIntegralCharacterMap_mapRingEquiv_comm` at `conjAe`)
gives `β̄ = τ⟨ζ_ind − ζ̄⟩`, so `β̄ − β = τ⟨ζ − ζ̄⟩` (`LinearMap.map_sub`).  The agreement
(`coherence_hagree_dadeMap`, `di = 1` by equal degrees) rewrites that to `νζ − νζ̄`.  `ζ_ind ∉ S`,
so
folding to the `S`-pair `{ζ, ζ̄}` via additivity is essential (the agreement only sees `S`). -/
theorem _root_.solution [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).beta.conj
        - (F.hypothesis78 i hodd hnilp C hFrob).beta
      = (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct)
        - (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
  classical
  set pf := F.sibleyPlacedFamily i hodd hnilp C hFrob with hpf
  set hyp := (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade with hhyp
  set dade := hyp.fullDadeIsometryData with hdade
  obtain ⟨j₁, hj₁ne, hj₁⟩ := F.exists_conjIndex_hypothesis78 i hodd hnilp C hFrob
  have hzeta : ∀ j, (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (pf.θ j : ClassFunction _ ℂ) :=
    fun j => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) j
  have hind : (F.hypothesis78 i hodd hnilp C hFrob).ind1H = pf.ind1H := rfl
  -- `ζ_ind = Ind 1_K` is real.
  have hind_real : ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H).conj
      = (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H := by
    rw [hzeta, hind, pf.triv, conj_induce]; exact congrArg _ trivialClassFunction_isReal
  -- `S`-memberships of `ζ` and `ζ̄ = ζ_{j₁}`.
  have hθ_ne : ∀ j, j ≠ pf.ind1H → pf.θ j ≠ trivialIrreducibleCharacter _ := fun j hj h =>
    hj (pf.inj (by simp only [h, pf.triv]))
  have hzd_mem : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct ∈
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [show (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 from rfl, hzeta 0]
    exact ⟨pf.θ 0, hθ_ne 0 (Ne.symm pf.ind1H_ne_zero), rfl⟩
  have hj₁_mem : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁ ∈
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [hzeta j₁]; exact ⟨pf.θ j₁, hθ_ne j₁ hj₁ne, rfl⟩
  have hsupp' : ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
        - (1 : ℂ) • (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
    rw [one_smul]; exact F.hypothesis78_zeta_sub_conj_support i hodd hnilp C hFrob hj₁
  have hagree := coherence_hagree_dadeMap hyp
    (F.coherence i hodd hnilp C hFrob) hzd_mem hj₁_mem
    (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  -- `dade.toDadeMap` on supported functions is `dadeIntegralCharacterMap hyp dade` (a `ℤ`-linear
  -- map).
  have hbridge : ∀ (φ : ClassFunction ↥(F.L i) ℂ)
      (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i)),
      dade.toDadeMap ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade φ := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
    rfl
  -- Support of `ζ_ind − ζ` (the `β`-argument) and its conjugate `ζ_ind − ζ̄`.
  have hiz_supp : ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H
        - (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) :=
    (F.hypothesis78 i hodd hnilp C hFrob).diff_support
  -- `β = τ_I (ζ_ind − ζ)`.
  have hbeta_eq : (F.hypothesis78 i hodd hnilp C hFrob).beta
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).ind1H
          - (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct) := by
    rw [← hbridge _ hiz_supp]; rfl
  -- `β̄ = τ_I (ζ_ind − ζ̄)`; combine via `map_sub` and the bridge back to `dade.toDadeMap`.
  have hconjbridgeL : ∀ X : ClassFunction ↥(F.L i) ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hconjbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hLHS : (F.hypothesis78 i hodd hnilp C hFrob).beta.conj
        - (F.hypothesis78 i hodd hnilp C hFrob).beta
      = dade.toDadeMap ⟨(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
          - (1 : ℂ) • (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁,
          (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [hbridge _ hsupp', hbeta_eq, hconjbridgeG (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      hyp dade _), ← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm hyp dade
      Complex.conjAe.toRingEquiv hiz_supp, ← hconjbridgeL, ← map_sub]
    congr 1
    rw [one_smul, ClassFunction.conj_sub, hind_real, ← hj₁]
    abel
  rw [hLHS, hagree, ← hj₁, F.hypothesis78_nu_eq i hodd hnilp C hFrob, one_smul]

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
