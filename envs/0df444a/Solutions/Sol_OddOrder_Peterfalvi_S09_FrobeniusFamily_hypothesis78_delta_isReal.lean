-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_delta_isReal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:27:26.637996+00:00
-- url     : https://prove2.me/submissions/60490fc5-cb01-40d4-aad9-a83e678fbb4d

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
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_zeta_ne_conj
import Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_beta_conj_sub

-- ===== OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

/-- **The residual `Δ = β − 1_G + νζ` is real** (Peterfalvi (7.9), delta-reality — pure algebra).
Given `β̄ − β = νζ − νζ̄` (`hbeta_conj_sub`, itself (A) `dadeMap_conj` + agreement + Dade linearity)
and `(νζ)‾ = ν(ζ̄)` (`hnu_conj`, (B) `coherence_extension_conj`), the two conjugate-difference terms
cancel: `Δ̄ − Δ = (β̄−β) + ((νζ)‾−νζ) = (νζ−νζ̄) + (νζ̄−νζ) = 0`.  `1_G` is real, so it drops out.
Feeds `cfdot_real_vchar_even` for the (7.9) `hdelta_even`. -/
theorem delta_isReal {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L)
    (hnu_conj : (H78.nu (H78.hyp76.zeta H78.zetaDistinct)).conj
        = H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj)
    (hbeta_conj_sub : H78.beta.conj - H78.beta
        = H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj) :
    ClassFunction.IsReal H78.delta := by
  have hd : H78.delta = H78.beta - Hypothesis71.constOne G
      + H78.nu (H78.hyp76.zeta H78.zetaDistinct) := rfl
  have hconstOne : (Hypothesis71.constOne G).conj = Hypothesis71.constOne G := by
    ext g; simp [ClassFunction.conj_apply, Hypothesis71.constOne_apply]
  have hbeta : H78.beta.conj = (H78.nu (H78.hyp76.zeta H78.zetaDistinct)
      - H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj) + H78.beta := by
    rw [← hbeta_conj_sub]; abel
  rw [ClassFunction.IsReal, hd, ClassFunction.conj_add, ClassFunction.conj_sub, hconstOne,
    hnu_conj, hbeta]
  abel

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley coherent extension commutes with complex conjugation** (Peterfalvi (5.9)(a); input
(B) of delta-reality).  `(ν χ).conj = ν χ.conj` for `χ` in the Sibley family `S`, by
`IsCoherent.extension_mapRingEquiv_comm` at `σ = conjugation` — the Sibley `S` is closed under
conjugation (`S_closedUnderConjugate`), consists of irreducibles
(`isIrreducibleCharacter_of_mem_S_of_frobenius`), and has the vanishing-at-1 support property
(`zSpan_S_support_subset_of_apply_one_eq_zero`). -/
theorem coherence_extension_conj [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    {χ : ClassFunction ↥(F.L i) ℂ}
    (hχS : χ ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S)
    (h2 : ∃ ψ ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S, ψ ≠ χ) :
    ((F.coherence i hodd hnilp C hFrob).extension χ).conj
      = (F.coherence i hodd hnilp C hFrob).extension χ.conj := by
  have hbridge : ∀ X : ClassFunction ↥(F.L i) ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  simp only [hbridge]
  exact (F.coherence i hodd hnilp C hFrob).extension_mapRingEquiv_comm subset_rfl
    (fun ψ hψ => mem_irreducibleCharacters.mpr
      ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob)
        |>.isIrreducibleCharacter_of_mem_S_of_frobenius hFrob hψ))
    (fun ψ hψ hψ1 => (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob)
      |>.zSpan_S_support_subset_of_apply_one_eq_zero hψ hψ1)
    Complex.conjAe.toRingEquiv
    (fun ψ hψ => by
      rw [← hbridge]
      exact (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S_closedUnderConjugate hψ)
    (fun ψ hψ =>
      (F.coherence i hodd hnilp C hFrob).extension_mem_ZIrr ψ (Submodule.subset_span hψ))
    hχS h2

/-- **The residual `Δ = β − 1_G + νζ` is real** (Frobenius; Peterfalvi (7.9)).  The generic
`delta_isReal` fed the two Frobenius inputs: `hnu_conj = (νζ)‾ = ν(ζ̄)` (= (B)
`coherence_extension_conj` at the distinguished `ζ ∈ S`, via `hypothesis78_nu_eq`) and
`hbeta_conj_sub = β̄ − β = νζ − νζ̄` (`hypothesis78_beta_conj_sub`).  Feeds
`cfdot_real_vchar_even` for the (7.9) `hdelta_even`. -/
theorem _root_.solution [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    ClassFunction.IsReal (F.hypothesis78 i hodd hnilp C hFrob).delta := by
  classical
  set pf := F.sibleyPlacedFamily i hodd hnilp C hFrob with hpf
  obtain ⟨j₁, hj₁ne, hj₁⟩ := F.exists_conjIndex_hypothesis78 i hodd hnilp C hFrob
  have hθ_ne : ∀ j, j ≠ pf.ind1H → pf.θ j ≠ trivialIrreducibleCharacter _ := fun j hj h =>
    hj (pf.inj (by simp only [h, pf.triv]))
  have hzeta : ∀ j, (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (pf.θ j : ClassFunction _ ℂ) :=
    fun j => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) j
  have hzd_mem : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct ∈
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [show (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 from rfl, hzeta 0]
    exact ⟨pf.θ 0, hθ_ne 0 (Ne.symm pf.ind1H_ne_zero), rfl⟩
  have hj₁_mem : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁ ∈
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [hzeta j₁]; exact ⟨pf.θ j₁, hθ_ne j₁ hj₁ne, rfl⟩
  have h2 : ∃ ψ ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S,
      ψ ≠ (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct :=
    ⟨_, hj₁_mem, by rw [hj₁]; exact (F.hypothesis78_zeta_ne_conj i hodd hnilp C hFrob).symm⟩
  have hnu_conj : ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct)).conj
      = (F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
    rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob]
    exact F.coherence_extension_conj i hodd hnilp C hFrob hzd_mem h2
  exact delta_isReal (F.hypothesis78 i hodd hnilp C hFrob) hnu_conj
    (F.hypothesis78_beta_conj_sub i hodd hnilp C hFrob)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
