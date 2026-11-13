-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.pair_cross_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:27:58.389758+00:00
-- url     : https://prove2.me/submissions/3d044aba-4711-4930-b9b1-f13b5ba85157

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence

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

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

/-- **The `(7.8)` coherent source set equals the (12.1) family `S`.** -/
theorem h78_sourceSet_eq : (data.h78 hG).sourceSet = data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    exact data.zeta_mem_Sset hidx
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := data.cover θ'
    have hj' : data.zeta j = ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, hj'⟩
    intro hjind
    apply induce_ne_trivialChar_induce data.kernelIn θ' hθ'_ne
    rw [← hj', show j = data.ind1H from hjind]
    change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce data.kernelIn
        ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
          ClassFunction _ ℂ)
    rw [data.triv]

/-- **The bundle coherence as an `IsCoherent` over the `(7.8)` `sourceSet`** (transport along
`h78_sourceSet_eq`, keeping the same extension `ν`). -/
noncomputable def isCoherentSourceSet :
    OddOrder.Peterfalvi.S07.IsCoherent data.typeIHyp.tau (data.h78 hG).sourceSet
      data.typeIHyp.A where
  nonzero := (data.h78_sourceSet_eq hG).symm ▸ data.coh.nonzero
  extension := data.coh.extension
  extension_inner_eq := fun φ ψ hφ hψ => data.coh.extension_inner_eq φ ψ
    (data.h78_sourceSet_eq hG ▸ hφ) (data.h78_sourceSet_eq hG ▸ hψ)
  extends_on_supported := fun φ hφ => data.coh.extends_on_supported φ
    (data.h78_sourceSet_eq hG ▸ hφ)
  extension_mem_ZIrr := fun φ hφ => data.coh.extension_mem_ZIrr φ
    (data.h78_sourceSet_eq hG ▸ hφ)

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

section Pairing

variable [Finite G] {L M : Subgroup G}

variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- **Family-wide cross-orthogonality** (Peterfalvi's "(4.1): `ℒ^{τ₁}` is orthogonal to
`ℳ^{τ₁}`"): `⟨φ_i^ν, χ_j^ν⟩ = 0` for **every** pair of nontrivial family indices.  Each
side pairs with its conjugate member (equal degree, distinct by odd order), the two
`ν`-differences are Dade images in the disjoint supports, and
`orthonormal_vchar_diff_ortho` concludes. -/
theorem _root_.solution
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H)
    {j : Fin (dataM.n + 1)} (hj : j ≠ dataM.ind1H) :
    ClassFunction.inner ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j)) = 0 := by
  obtain ⟨i', hi'ne, hi'⟩ := dataL.exists_conjIndex_at hG hi
  obtain ⟨j', hj'ne, hj'⟩ := dataM.exists_conjIndex_at hG hj
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by
    rw [dataL.h78_ind1H_eq]; exact hi
  have hj_h78 : j ≠ (dataM.h78 hG).ind1H := by
    rw [dataM.h78_ind1H_eq]; exact hj
  refine orthonormal_vchar_diff_ortho
    ((dataL.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataL.isCoherentSourceSet hG) rfl hi_h78)
    ((dataL.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataL.isCoherentSourceSet hG) rfl hi'ne)
    ((dataM.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataM.isCoherentSourceSet hG) rfl hj_h78)
    ((dataM.h78 hG).nu_zeta_mem_ZIrr_of_isCoherent (dataM.isCoherentSourceSet hG) rfl hj'ne)
    (dataL.nu_zeta_norm_one hG hi_h78) (dataL.nu_zeta_norm_one hG hi'ne)
    (dataM.nu_zeta_norm_one hG hj_h78) (dataM.nu_zeta_norm_one hG hj'ne)
    (dataL.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hi hi'ne hi')
    (dataM.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hj hj'ne hj')
    ?_ ?_ ?_
  · -- The two `ν`-differences live in the disjoint Dade supports.
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp
      (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).dadeSupport_disjoint
      (dataL.nu_zeta_sub_conj_support_at hG hi hi'ne hi' hg₁)
      (dataM.nu_zeta_sub_conj_support_at hG hj hj'ne hj' hg₂)
  · -- Equal degrees on the `L`-side: the difference vanishes at `1 ∉ Ã(L)`.
    have hz : ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
        - (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i')) (1 : G) = 0 := by
      by_contra h
      exact (dataL.h78 hG).hyp76.hyp71.hyp.one_notMem_dadeSupport
        (dataL.nu_zeta_sub_conj_support_at hG hi hi'ne hi'
          (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  · -- Equal degrees on the `M`-side.
    have hz : ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j)
        - (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j')) (1 : G) = 0 := by
      by_contra h
      exact (dataM.h78 hG).hyp76.hyp71.hyp.one_notMem_dadeSupport
        (dataM.nu_zeta_sub_conj_support_at hG hj hj'ne hj'
          (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz

end Pairing

end OddOrder.Peterfalvi.S16
