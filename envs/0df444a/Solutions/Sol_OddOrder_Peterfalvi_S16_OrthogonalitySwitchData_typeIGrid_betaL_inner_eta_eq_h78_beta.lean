-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.typeIGrid_betaL_inner_eta_eq_h78_beta
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:23:32.971206+00:00
-- url     : https://prove2.me/submissions/16624d8f-a56d-475e-967b-6b86bdc0f4a7

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/RhoConstancy.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_mSide_dadeSupport_avoids_regular

-- ===== OddOrder/Peterfalvi/S14_MaximalI/RhoConstancy.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5) support, packaged for the Dade isometry** (the Frobenius witness case): the
difference `χ₁ − χ₂` of two equal-degree members of `S` is supported in `A(L) = ambientA` (as
`supportInSubgroup ambientA L`), so it is a `SupportedClassFunctions` to which the Dade isometry and
the `chiRho_adjoint` reciprocity apply.  From `Sset_diff_vanishes_off_H_sharp`
(`χ₁ − χ₂` vanishes off `H^# = H ∖ {1}`) and `hAH : A(L) = H^#`
(`mem_supportInSubgroup_sharp_subgroupOf_iff`).  Feeds the `A1xi12` step of the (12.5) `o_rpsi_S`
Fact-A. -/
theorem Sset_diff_support_subset_ambientA {L : Subgroup G} (hyp : Hypothesis L)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L))
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1}) :
    (χ₁ - χ₂).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hnot : ¬((x : G) ∉ hyp.H ∨ x = 1) := fun h =>
    hx (Sset_diff_vanishes_off_H_sharp hyp hχ₁ hχ₂ hdeg h)
  push Not at hnot
  exact (OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
    hyp.typeI.typeF.H hAH x).mpr ⟨Subgroup.mem_subgroupOf.mpr hnot.1, hnot.2⟩

end OddOrder.Peterfalvi.S14

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

/-- **The conjugate of any nontrivial family member is a family member**:
for `i ≠ ind1H` there is `i' ≠ ind1H` with `ζ_{i'} = ζ̄_i`. -/
theorem exists_conjIndex_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    ∃ i', i' ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta i).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ i)) : ClassFunction _ ℂ) := by
    rw [data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ i)).symm
  obtain ⟨i', hi'_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ i))
  have hi'_conj : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hi'_range
  refine ⟨i', ?_, hi'_conj⟩
  intro hi'1
  -- else `ζ̄_i = ζ_{ind1H} = Ind 1_H` is real, so `ζ_i = Ind 1_H`, contra `i ≠ ind1H`.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  refine hi (data.inj ?_)
  have h1 : ((data.h78 hG).hyp76.zeta i).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    rw [← hi'_conj, hi'1]
  calc (data.h78 hG).hyp76.zeta i
      = (((data.h78 hG).hyp76.zeta i).conj).conj := (ClassFunction.conj_conj _).symm
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by rw [h1, hind_real]

/-- **No nontrivial family member is real** (odd order): `ζ_i ≠ ζ̄_i` for `i ≠ ind1H`. -/
theorem zeta_ne_conj_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta i ≠ ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial hi)
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_i(1) = [L:H]·θ_i(1) ≥ [L:H] > 1`, so `ζ_i` is nontrivial.
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  have hdeg : (data.h78 hG).hyp76.zeta i (1 : ↥L)
      = ((data.kernelIn).index : ℂ) * (di : ℂ) := by
    rw [data.h78_zeta_eq]
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) = _
    rw [ClassFunction.induce_apply_one, hdi]
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta i, hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta i = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((data.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have : (data.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (data.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_i − ζ̄_i` is supported on `A(L)`** for any `i ≠ ind1H`. -/
theorem zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)}
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).hyp76.zeta i - (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hi', ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · intro hx1
    apply hx
    rw [hx1]
    -- `ζ_i(1)` is real (`induce_apply_one_star`).
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sub_self]

/-- **`ζ_i^ν − ζ̄_i^ν` is supported in the Dade support** for any `i ≠ ind1H`. -/
theorem nu_zeta_sub_conj_support_at (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
        - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')).support
      ⊆ (data.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  have := data.kernelIn_normal
  have hzi_mem : (data.h78 hG).hyp76.zeta i ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]; exact data.zeta_mem_Sset hi
  have hi'_mem : (data.h78 hG).hyp76.zeta i' ∈ data.typeIHyp.Sset := by
    rw [data.h78_zeta_eq]
    exact data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta i
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta i').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support_at hG hi'
  have hagree := coherence_hagree_dadeMap data.typeIHyp.dadeData.dade
    data.coh hzi_mem hi'_mem (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq : (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
      - (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')
      = (data.typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeMap
          ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [data.h78_nu_eq,
      ← one_smul ℂ (data.coh.extension ((data.h78 hG).hyp76.zeta i'))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade := (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- **Each `ζ_i^ν` (`i ≠ ind1H`) is a unit-norm virtual character.** -/
theorem nu_zeta_norm_one {i : Fin (data.n + 1)} (hi : i ≠ (data.h78 hG).ind1H) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)) = 1 := by
  have := data.kernelIn_normal
  rw [(data.h78 hG).nu_isometry i i hi hi]
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial (by rw [← data.h78_ind1H_eq hG]; exact hi))
  exact IsIrreducibleCharacter.inner_self_eq_one hirr

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

/-- **`⟨ζ_i^ν, ζ̄_i^ν⟩ = 0`**: the conjugate pair is orthonormal (`ν`-isometry +
distinct irreducibles). -/
theorem nu_zeta_inner_nu_conj_eq_zero (hodd : Odd (Nat.card G))
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')) = 0 := by
  rw [(data.h78 hG).nu_isometry i i' hi hi'_ne]
  have hirr_i := data.zeta_irreducible_at hG hi
  have hirr_i' : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i') :=
    data.zeta_irreducible_at hG (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hne : (data.h78 hG).hyp76.zeta i ≠ (data.h78 hG).hyp76.zeta i' := by
    rw [hi']
    exact data.zeta_ne_conj_at hG hi hodd
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_i⟩ : IrreducibleCharacter ↥L) ⟨_, hirr_i'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (13.19.b), the `η`-grid orthogonality of *every* coherent image `ζ_k^ν`**
(the Coq `o_tauLeta` for the whole family, not just the distinguished index).  For any family
member `k ≠ ind1H`, the coherent image `ζ_k^ν = (dataM.h78 hG).nu (ζ_k)` is orthogonal to the
entire `η`-grid.  Identical (3.6)–(3.8)/(13.19.b) engine as `caseB_eta_orthogonal_psi`, but with
the distinguished index `zetaDistinct` replaced by an arbitrary `k`: `ζ_k^ν` has unit norm
(`nu_zeta_norm_one`), its conjugate partner `ζ_{k'}^ν` (`exists_conjIndex_at`, generic in the
index) is a distinct unit-norm virtual character (`nu_zeta_inner_nu_conj_eq_zero`), and the
conjugate difference `ζ_k^ν − ζ_{k'}^ν` (supported in `Ã(M)`, `nu_zeta_sub_conj_support_at`,
also generic) vanishes on `Ŵ^G` by the same (13.19.a) Dade-support avoidance `hDadeAvoid`. -/
theorem caseB_eta_orthogonal_nu_zeta_at [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {M : Subgroup G} (dataM : TypeICoherent78Data M)
    (hDadeAvoid : ∀ x ∈ conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport)
    {k : Fin (dataM.n + 1)} (hk : k ≠ (dataM.h78 hG).ind1H) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j)
        ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)) = 0 := by
  classical
  -- the kernel-index datum for `k` and its conjugate partner `k'`
  have hkne : k ≠ dataM.ind1H := by rwa [dataM.h78_ind1H_eq] at hk
  obtain ⟨k', hk'_ne, hk'⟩ := dataM.exists_conjIndex_at hG hkne
  -- engine inputs from the coherence bundle
  have hpsiZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k) ∈ ZIrr G := by
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hkne))
  have hconjZ : (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k') ∈ ZIrr G := by
    have hk'ne_data : k' ≠ dataM.ind1H := by rw [← dataM.h78_ind1H_eq]; exact hk'_ne
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq]
    exact dataM.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataM.zeta_mem_Sset hk'ne_data))
  have hpsi1 := dataM.nu_zeta_norm_one hG hk
  have hconj1 := dataM.nu_zeta_norm_one hG hk'_ne
  have hcross := dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hkne hk'_ne hk'
  have hsupp := dataM.nu_zeta_sub_conj_support_at hG hkne hk'_ne hk'
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta k')) x = 0 := by
    intro x hx
    by_contra hval
    exact hDadeAvoid x hx (hsupp (ClassFunction.mem_support.mpr hval))
  exact eta_orthogonal_of_norm_one_pair_vanish hyp hpsiZ hconjZ hpsi1 hconj1 hcross hvanish

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (13.19.b), invariance of the `eta`-grid coefficients under the choice of
distinguished coherent-family member.**

Let `grid.phi` be the member chosen by the §13 type-I grid producer and let `zeta 0` be the member
chosen by the §7.8 coherent bundle.  Both lie in the same coherent family and have the common
degree `[M : M_F]`.  Hence their difference is supported in `A(M)`, so the Dade map sends it to the
difference of their coherent images.  Every coherent image is orthogonal to the `eta`-grid by
(13.19.b); consequently replacing `grid.phi` by `zeta 0` changes the associated Dade `beta` by a
function orthogonal to every `eta_ij`.

This is the choice-free synchronization needed by (14.11.2): it deliberately asserts equality of
the grid coefficients, not equality of the two `beta` class functions (which need not hold for
different distinguished family members). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M)
    (grid : OddOrder.Peterfalvi.S15.TypeIOrthogonalityGridData
      hyp.base dataM)
    (hphi : grid.phi ∈ dataM.typeIHyp.Sset) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
        ClassFunction.inner grid.betaL (hyp.base.eta i j) =
          ClassFunction.inner (coherentBeta hG dataM) (hyp.base.eta i j) := by
  classical
  intro fintypeG invertibleG i j
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have := dataM.kernelIn_normal
  -- The two selected family members have the same degree, namely the complement index.
  have he : grid.e = dataM.kernelIn.index := by
    rw [← grid.e_eq_index]
    change ((maxNilpotentNormalHall M).subgroupOf M).index =
      ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M).index
    rw [dataM.typeIHyp.typeI.typeF.H_eq]
  have hdeg : dataM.zeta 0 (1 : ↥M) = grid.phi (1 : ↥M) := by
    rw [dataM.deg0, grid.phi_degree_eq_e, he]
  -- Their difference lies in the supported coherent lattice, so `tau = tau1` on it.
  have hsharp : dataM.typeIHyp.ambientA = (dataM.kernel : Set G) \ {1} := by
    simpa [OddOrder.Peterfalvi.S14.Hypothesis.ambientA] using dataM.typeIA_eq_sharp
  have hsupp : (dataM.zeta 0 - grid.phi).support ⊆ dataM.typeIHyp.A := by
    simpa [OddOrder.Peterfalvi.S14.Hypothesis.A,
      OddOrder.Peterfalvi.S14.Hypothesis.ambientA] using
      (OddOrder.Peterfalvi.S14.Sset_diff_support_subset_ambientA dataM.typeIHyp
        (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)) hphi hdeg hsharp)
  have hagree : dataM.typeIHyp.tau (dataM.zeta 0 - grid.phi) =
      dataM.coh.extension (dataM.zeta 0) - dataM.coh.extension grid.phi := by
    rw [← map_sub]
    exact (dataM.coh.extends_on_supported (dataM.zeta 0 - grid.phi)
      ⟨Submodule.sub_mem _
          (Submodule.subset_span (dataM.zeta_mem_Sset (Ne.symm dataM.ind1H_ne_zero)))
          (Submodule.subset_span hphi),
        hsupp⟩).symm
  -- The canonical §7.8 beta is `tau (Ind 1 - zeta 0)`.
  have hbeta : coherentBeta hG dataM = dataM.typeIHyp.tau
      (ClassFunction.induce ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)
        (trivialClassFunction ↥((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)) - dataM.zeta 0) := by
    rw [coherentBeta]
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
    change dataM.typeIHyp.toHypothesis71.τ _ = dataM.typeIHyp.tau _
    rw [dataM.typeIHyp.toHypothesis71_tau_apply]
    apply congrArg dataM.typeIHyp.tau
    change (dataM.h78 hG).hyp76.zeta (dataM.h78 hG).ind1H -
        (dataM.h78 hG).hyp76.zeta (dataM.h78 hG).zetaDistinct = _
    rw [dataM.h78_ind1H_eq, dataM.h78_zeta_eq,
      dataM.h78_zetaDistinct_eq, dataM.h78_zeta_eq]
    change ClassFunction.induce dataM.kernelIn
        (dataM.θ dataM.ind1H : ClassFunction _ ℂ) - dataM.zeta 0 = _
    rw [dataM.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  -- Thus the difference of the two beta functions is the coherent-image difference.
  have hbetaDiff : grid.betaL - coherentBeta hG dataM =
      dataM.coh.extension (dataM.zeta 0) - dataM.coh.extension grid.phi := by
    rw [grid.betaL_eq, hbeta, ← hagree, ← map_sub]
    apply congrArg dataM.typeIHyp.tau
    change (ClassFunction.induce ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)
        (trivialClassFunction ↥((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)) - grid.phi) -
      (ClassFunction.induce ((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)
        (trivialClassFunction ↥((dataM.typeIHyp.typeI.typeF.H).subgroupOf M)) - dataM.zeta 0) =
      dataM.zeta 0 - grid.phi
    abel
  -- Realize `grid.phi` as one of the placed induced family members.
  obtain ⟨theta, htheta, hphi_eq⟩ := hphi
  obtain ⟨k, hk⟩ := dataM.cover theta
  have hkphi : dataM.zeta k = grid.phi := hk.trans hphi_eq.symm
  have hk_ne : k ≠ dataM.ind1H := by
    intro hk_ind
    apply OddOrder.Peterfalvi.S09.Cert.induce_ne_trivialChar_induce
      dataM.kernelIn theta htheta
    calc
      ClassFunction.induce dataM.kernelIn (theta : ClassFunction _ ℂ) = grid.phi := hphi_eq.symm
      _ = dataM.zeta k := hkphi.symm
      _ = dataM.zeta dataM.ind1H := by rw [hk_ind]
      _ = ClassFunction.induce dataM.kernelIn
          (trivialIrreducibleCharacter ↥dataM.kernelIn : ClassFunction _ ℂ) := by
        change ClassFunction.induce dataM.kernelIn
            (dataM.θ dataM.ind1H : ClassFunction _ ℂ) = _
        rw [dataM.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  have hDadeAvoid := mSide_dadeSupport_avoids_regular (hyp := hyp) hG hnoV hncH0C hMmax dataM
  have hzero_ne : (0 : Fin (dataM.n + 1)) ≠ (dataM.h78 hG).ind1H := by
    rw [dataM.h78_ind1H_eq]
    exact Ne.symm dataM.ind1H_ne_zero
  have hk_ne' : k ≠ (dataM.h78 hG).ind1H := by
    rw [dataM.h78_ind1H_eq]
    exact hk_ne
  have horth_zero : ClassFunction.inner (dataM.coh.extension (dataM.zeta 0))
      (hyp.base.eta i j) = 0 := by
    have h := caseB_eta_orthogonal_nu_zeta_at
      hG hyp.base dataM hDadeAvoid hzero_ne i j
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq] at h
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  have horth_phi : ClassFunction.inner (dataM.coh.extension grid.phi)
      (hyp.base.eta i j) = 0 := by
    have h := caseB_eta_orthogonal_nu_zeta_at
      hG hyp.base dataM hDadeAvoid hk_ne' i j
    rw [dataM.h78_nu_eq, dataM.h78_zeta_eq] at h
    rw [← hkphi, OddOrder.RepresentationTheory.inner_conj_symm, h, star_zero]
  have hdiff : ClassFunction.inner (grid.betaL - coherentBeta hG dataM)
      (hyp.base.eta i j) = 0 := by
    rw [hbetaDiff, ClassFunction.inner_sub_left, horth_zero, horth_phi, sub_zero]
  rw [ClassFunction.inner_sub_left, sub_eq_zero] at hdiff
  exact hdiff

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
