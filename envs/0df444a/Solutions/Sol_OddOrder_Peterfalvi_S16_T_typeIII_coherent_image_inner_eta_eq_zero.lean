-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.T_typeIII_coherent_image_inner_eta_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:46.348767+00:00
-- url     : https://prove2.me/submissions/9f49c843-b194-423a-bc57-fa290d5c8e54

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDadeMap_eq_full_typeP1DadeMap_of_support

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.3.b), T-side coherent images are orthogonal to the shared `η`-grid.**

This is the subfamily form used in (14.9), Coq `coherent_ortho_cycTIiso`.  The coherent
conjugate difference agrees with the Dade map on `A₁(T) = T_σ#`.  The latter is the restriction
of the full type-`P₁` `A₀(T)` Dade map.  For a regular element of the shared cyclic group
`W = W₁ × W₂`, the reconciled T-side type-`P` datum identifies that element with its
`typePV`; the full Dade map therefore reads the source difference there, which is zero because
the source is `A₁(T)`-supported.  Conjugacy invariance gives vanishing on the full regular-set
saturation, and the (3.7)--(3.8) norm-two engine
`eta_orthogonal_of_norm_one_pair_vanish` gives the desired individual orthogonality. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoReal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hsupp : ∀ ζ ∈ S, (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ : ClassFunction ↥hyp.base.T ℂ} (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner (coh.extension ζ) (hyp.base.eta i j) = 0 := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have := hyp.base.finiteG
  classical
  let dataT := (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose
  have hdata := (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose_spec
  have hU : dataT.U = hyp.base.V := hdata.1
  have hW1 : dataT.W1 = hyp.base.W2 := hdata.2.1
  have hW2 : dataT.W2 = hyp.base.W1 := hdata.2.2
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := by
    have hcls := OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
    exact (hcls.2.2.1.mp (Or.inl hIII)).1
  let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
    hG hyp.base.T_maximal dataT hP1).some
  have hPA : OddOrder.GroupTheory.typePA hyp.base.T dataT =
      OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.Peterfalvi.S10.typePA_eq_sigmaSharp_of_isTypeP1
      hG hyp.base.T_maximal dataT hP1
  have hA1A0 : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T ⊆
      OddOrder.GroupTheory.typePA0 hyp.base.T dataT := by
    rw [← hPA]
    exact Set.subset_union_left
  have hζc : ζ.conj ∈ S := hconj hζ
  have hdiffSpan : ζ - ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.base.T) S :=
    Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hdiffSupp := hsupp ζ hζ
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :=
    ⟨hdiffSpan, hdiffSupp⟩
  have hfullSupp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 hyp.base.T dataT) hyp.base.T :=
    hdiffSupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA1A0)
  have hmaps : tSideDadeMap hyp hG (ζ - ζ.conj) =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData) (ζ - ζ.conj) := by
    simpa only [full] using
      tSideDadeMap_eq_full_typeP1DadeMap_of_support hG hyp dataT hP1 hdiffSupp
  have hextDiff : coh.extension ζ - coh.extension ζ.conj =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData) (ζ - ζ.conj) := by
    rw [← hmaps, ← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  have hW : dataT.W = hyp.base.W := by
    rw [dataT.W_eq, hW1, hW2, hyp.base.W_eq_join, sup_comm]
  have hV : OddOrder.GroupTheory.typePV hyp.base.T dataT =
      (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) := by
    simp only [OddOrder.GroupTheory.typePV, hW, hW1, hW2, Set.union_comm]
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      (coh.extension ζ - coh.extension ζ.conj) x = 0 := by
    intro x hx
    obtain ⟨w, hw, g, hg⟩ := hx
    rw [hextDiff]
    rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
      (full.dade.fullDadeIsometryData) (ζ - ζ.conj)).of_isConj
        (isConj_iff.mpr ⟨g, hg⟩)]
    have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.base.T dataT := hV.symm ▸ hw
    have hwA0 : w ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT :=
      Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support full.dade
      (full.dade.fullDadeIsometryData) hfullSupp]
    let a : {a : G // a ∈ OddOrder.GroupTheory.typePA0 hyp.base.T dataT} := ⟨w, hwA0⟩
    have hwh : w ∈ full.dade.hCoset a := ⟨1, full.dade.H a |>.one_mem, by simp [a]⟩
    rw [full.dade.isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
    by_contra hne
    have hwSupp : (⟨w, full.dade.mem_L hwA0⟩ : ↥hyp.base.T) ∈
        (ζ - ζ.conj).support := ClassFunction.mem_support.mpr hne
    have hwSigma : w ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T := hdiffSupp hwSupp
    have hwDeriv : w ∈ derivedInG hyp.base.T := by
      rw [OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma
        hG hyp.base.T_maximal hP1]
      exact hwSigma.1
    exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived dataT hwV) hwDeriv
  have hpsiZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span hζ)
  have hconjZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζc)
  have hpsi1 : ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 := by
    rw [coh.extension_inner_eq ζ ζ (Submodule.subset_span hζ) (Submodule.subset_span hζ)]
    exact hζirr.inner_self_eq_one
  have hconj1 : ClassFunction.inner (coh.extension ζ.conj) (coh.extension ζ.conj) = 1 := by
    rw [coh.extension_inner_eq ζ.conj ζ.conj (Submodule.subset_span hζc)
      (Submodule.subset_span hζc)]
    exact hζirr.conj.inner_self_eq_one
  have hcross : ClassFunction.inner (coh.extension ζ) (coh.extension ζ.conj) = 0 := by
    rw [coh.extension_inner_eq ζ ζ.conj (Submodule.subset_span hζ)
      (Submodule.subset_span hζc), OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj,
      if_neg (fun h => hnoReal hζ h.symm)]
  intro i j
  have h := eta_orthogonal_of_norm_one_pair_vanish hyp.base hpsiZ hconjZ hpsi1 hconj1
    hcross hvanish i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]

end OddOrder.Peterfalvi.S16
