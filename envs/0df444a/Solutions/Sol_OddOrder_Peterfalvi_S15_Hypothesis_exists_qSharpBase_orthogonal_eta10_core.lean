-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.exists_qSharpBase_orthogonal_eta10_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:00:05.660248+00:00
-- url     : https://prove2.me/submissions/bd31385f-4d1c-4171-a53e-ebcaa52d6db9

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_Tau1T.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

-- ===== OddOrder/Peterfalvi/S15_Tau1T.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c)-at-`T`, the ν-row formula for `τ₁T = tau1T_ofHonest`** (mirror of
`tau1S_ofHonest_muColumn_formula`; Coq `FTtypeP_coherence` with `typeP_TIred_coherent`'s
global-sign disjunction, transposed): the (9.11)-`T` coherent extension sends every reducible
ν-row sum `ν_i = ∑_j ν_{ij}` (`i ≠ 0`) to the aligned `η`-row sum `∑_j η_{ij}` — either
uniformly, or (the `q = 3` sign-flip exception) with a global negative sign and the two nonzero
rows swapped.  The `.choose_spec` of the pinned carrier. -/
theorem Hypothesis.tau1T_ofHonest_nuRow_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = ∑ j : Fin hyp.p, hyp.eta i j) ∨
    (hyp.q = 3 ∧ ∀ i i' : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      i' ≠ ⟨0, hyp.q_prime.pos⟩ → i ≠ i' →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = -∑ j : Fin hyp.p, hyp.eta i' j) :=
  (hyp.sSet_coherent_indT_A_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief).choose_spec

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8), the coefficient-zero chosen `Q^#` base**: choose a nonzero
`ν`-row different from the row paired with `η₁₀`, transport its `QD`-source to `Q` using
`D = ⊥`, and retain both `Q ⊄ Ker φ₀` and
`⟨τ₁T(Ind_Q^T φ₀), η₁₀⟩ = 0`.

This is the faithful case-B replacement for an unavailable assumption that `Ind_Q^T φ₀`
itself be irreducible. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.Q.subgroupOf hyp.T),
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∧
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0 := by
  classical
  let i₁ : Fin hyp.q := ⟨1, hyp.q_prime.one_lt⟩
  have h2lt : 2 < hyp.q := by
    have := hyp.three_le_q
    omega
  let i₂ : Fin hyp.q := ⟨2, h2lt⟩
  have hi₁0 : i₁ ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) one_ne_zero
  have hi₂0 : i₂ ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hi₂1 : i₂ ≠ i₁ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hetaRowZero : ∀ a : Fin hyp.q, a ≠ i₁ →
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta a j) hyp.eta10 = 0 := by
    intro a ha
    rw [show hyp.eta10 = hyp.eta i₁ ⟨0, hyp.p_prime.pos⟩ from rfl,
      OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hyp.eta_orthonormal a i₁ j ⟨0, hyp.p_prime.pos⟩,
      if_neg (fun h => ha h.1)]
  obtain ⟨s, hs0, hsOrth⟩ : ∃ s : Fin hyp.q,
      s ≠ ⟨0, hyp.q_prime.pos⟩ ∧
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (∑ j : Fin hyp.p, hyp.nu s j)) hyp.eta10 = 0 := by
    rcases hyp.tau1T_ofHonest_nuRow_formula hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief with
      hclean | ⟨_hq3, hflip⟩
    · refine ⟨i₂, hi₂0, ?_⟩
      rw [hclean i₂ hi₂0]
      exact hetaRowZero i₂ hi₂1
    · refine ⟨i₁, hi₁0, ?_⟩
      rw [hflip i₁ i₂ hi₁0 hi₂0 (fun h => hi₂1 h.symm),
        ClassFunction.inner_neg_left, hetaRowZero i₂ hi₂1, neg_zero]
  have hKQ : hyp.K.subgroupOf hyp.T = hyp.Q.subgroupOf hyp.T := by
    have h : hyp.K = hyp.Q := by
      change hyp.Q ⊔ hyp.D = hyp.Q
      rw [hD, sup_bot_eq]
    rw [h]
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hQnorm : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr (by
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  obtain ⟨θs, hθsirr, -, hνeqK⟩ := hyp.nu_i_isIndQD hG pins s hs0
  set θsQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKQ.symm).toMonoidHom θs with hθsQdef
  have hθsQirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θsQ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKQ.symm).surjective hθsirr
  have hνeqQ : (∑ j : Fin hyp.p, hyp.nu s j)
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θsQ := by
    rw [hνeqK]
    exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ.symm θs).symm
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  set HU : Subgroup ↥hyp.T := huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    huSub_eq_derivedInG_subgroupOf data
  have hQle : hyp.Q.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]
    refine Subgroup.subgroupOf_mono hyp.T ?_
    rw [hyp.T_deriv_eq_QV]
    exact le_sup_left
  have hνmem : (∑ j : Fin hyp.p, hyp.nu s j) ∈ sSet data :=
    sOf_subset_sSet data chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief s hs0)
  have hQkerNu : ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (∑ j : Fin hyp.p, hyp.nu s j)) := by
    intro hsub
    obtain ⟨ξ, hξ, hξeq⟩ := hνmem
    have hξker : ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥HU ℂ)) := hξ
    obtain ⟨x, hxIn, hxKer⟩ := Set.not_subset.mp hξker
    have hxQ : ((x : ↥hyp.T)) ∈ hyp.Q.subgroupOf hyp.T := by
      have hxH : ((x : ↥hyp.T)) ∈ data.H.subgroupOf hyp.T :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hxIn)
      rwa [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hxH
    have hxker2 : ((x : ↥hyp.T)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce HU (ξ : ClassFunction ↥HU ℂ)) := by
      have hx := hsub hxQ
      rwa [hξeq, induceHU_eq_induce data] at hx
    have hdesc := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ξ.isIrreducible x.2 hxker2
    exact hxKer (by simpa using hdesc)
  have hθsQfull : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf
      (hyp.Q.subgroupOf hyp.T) : Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θsQ) := by
    intro hker
    apply hQkerNu
    rw [hνeqQ]
    exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf le_rfl θsQ hker
  refine ⟨⟨θsQ, hθsQirr⟩, hθsQfull, ?_⟩
  rw [← hνeqQ]
  exact hsOrth

end

end OddOrder.Peterfalvi.S15
