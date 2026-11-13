-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.coherent_extension_orthogonal_eta_of_mem_Sset
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:37.558772+00:00
-- url     : https://prove2.me/submissions/75976dcd-d7da-4fe1-bb23-38a96acebac0

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S04_Hypothesis_exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_zeta_index_of_mem_Sset

-- ===== OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean =====
namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

variable [Finite G]

/-- **Conjugate subgroups have the same type I status**: if `L` is type I and `conj g • L = M`,
then `M` is type I.  The Peterfalvi (13.17.b) input ruling out conjugacy of a type-`I` subgroup to
the type-II subgroups `S`, `T`. -/
theorem isTypeI_of_conj {L M : Subgroup G} (h : IsTypeI L) {g : G}
    (hconj : MulAut.conj g • L = M) : IsTypeI M :=
  hconj ▸ isTypeI_pointwise_smul (MulAut.conj g) h

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Type is conjugacy-invariant** (the (13.17.a/b) `L ~ S`/`L ~ T` rule-out): a type-`I` maximal
subgroup `L` is not conjugate to any non-type-`I` maximal subgroup `M`.  If `conj g • L = M` then
`M` would be type `I` (`isTypeI_of_conj`, the automorphism-equivariance of the Peterfalvi taxonomy
— `OddOrder.GroupTheory.MaximalSubgroupTypeConj`), contradicting
`not_isTypeI_of_isTypeNonI`.  This is **gate-4 piece 1**, now discharged (sorry-free, axiom-clean);
reusable across the §16 conjugacy arguments. -/
theorem not_conj_of_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L M : Subgroup G} (hLI : IsTypeI L) (hMmax : M ∈ maximalSubgroups G)
    (hMnonI : IsTypeNonI M) : ¬ ∃ g : G, MulAut.conj g • L = M :=
  fun ⟨_g, hg⟩ =>
    OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hMmax hMnonI
      (OddOrder.GroupTheory.isTypeI_of_conj hLI hg)

end OddOrder.Peterfalvi.S15

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

-- ===== OddOrder/Peterfalvi/S15_SAndTGrid.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`A(M) ⊆ H^#` for a Frobenius type-I maximal** (with `sharpSubgroup_H_subset_typeIA`,
equality — Coq `FTsupp_Frobenius`): an element of the type-I support `A(M)` centralizes some
`y ∈ H^#`, and in a Frobenius group the centralizer of a nontrivial kernel element lies in the
kernel (`IsFrobeniusGroup.centralizer_kernel_le`, Isaacs Thm 6.4). -/
theorem typeIA_subset_sharpSubgroup_of_frobenius [Finite G] {M : Subgroup G}
    (data : TypeIData M) {E : Subgroup ↥M}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M) E) :
    typeIA M data ⊆ sharpSubgroup data.typeF.H := by
  rintro x ⟨hxM, hx1, y, hy, hxc⟩
  have hyM : y ∈ M := data.typeF.H_le hy.1
  have hyH' : (⟨y, hyM⟩ : ↥M) ∈ data.typeF.H.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact hy.1
  have hy1' : (⟨y, hyM⟩ : ↥M) ≠ 1 := fun h => hy.2 (by
    simpa using congrArg Subtype.val h)
  have hxc' : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer ({⟨y, hyM⟩} : Set ↥M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxc
    exact Subtype.ext (by push_cast; exact hcomm)
  have hxH' := hF.centralizer_kernel_le _ hyH' hy1' hxc'
  rw [Subgroup.mem_subgroupOf] at hxH'
  exact ⟨hxH', hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support avoidance** (Coq `tiA_PWG` restricted to `Ŵ^G`): for
a type-I maximal `L`, the Dade support `Ã(L)` avoids the regular-set saturation
`Ŵ^G = (W ∖ (W₁ ∪ W₂))^G` — an `Ã(L)`-element has a prime divisor of `|L_F|` in its order
(`exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport` + `A(L) ⊆ L_F^#`), while a
`Ŵ^G`-element has order dividing `|W| = p q`, coprime to `|L_F|` ((8.17.a)
`card_LF_coprime_pq`).  The conjugation-free core of `typeIBetaL_betaS_disjoint_support`. -/
theorem typeI_dadeSupport_avoids_regular [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) :
    ∀ x ∈ OddOrder.GroupTheory.conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      x ∉ typeISetup.dadeData.dade.dadeSupport := by
  intro x hx hxD
  -- L-side: a prime `r ∣ |L_F|` divides `orderOf x`
  obtain ⟨a, haA, r, hr, hra, hrx⟩ :=
    typeISetup.dadeData.dade.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport hxD
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV typeISetup.maximal
    ⟨typeISetup.typeI⟩
  have hHeq : frob₀.typeI.typeF.H = typeISetup.typeI.typeF.H :=
    frob₀.typeI.typeF.H_eq.trans typeISetup.typeI.typeF.H_eq.symm
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeISetup.typeI.typeF.H).subgroupOf L) frob₀.complement := by
    have h := frob₀.frobenius
    rwa [hHeq] at h
  have haH := typeIA_subset_sharpSubgroup_of_frobenius typeISetup.typeI hfrob haA
  have hrLF : r ∣ Nat.card ↥(maxNilpotentNormalHall L) := by
    refine hra.trans ?_
    have hdvd := Subgroup.orderOf_dvd_natCard typeISetup.typeI.typeF.H haH.1
    rwa [typeISetup.typeI.typeF.H_eq] at hdvd
  -- regular side: `orderOf x = orderOf w ∣ |W| = p q`
  obtain ⟨w, hw, c, hcx⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hordx : orderOf x = orderOf w := by
    rw [← hcx]
    have hinj : orderOf ((MulAut.conj c).toMonoidHom w) = orderOf w :=
      orderOf_injective (MulAut.conj c).toMonoidHom (MulEquiv.injective _) _
    rw [← hinj]
    congr 1
  have hword : orderOf w ∣ hyp.p * hyp.q := by
    have h := Subgroup.orderOf_dvd_natCard hyp.W hw.1
    rwa [card_W_eq_pq hyp] at h
  have hxord : orderOf x ∣ hyp.p * hyp.q := by rw [hordx]; exact hword
  have hrpq : r ∣ hyp.p * hyp.q := hrx.trans hxord
  -- a prime dividing both `|L_F|` and `p·q` contradicts (8.17.a)
  have hnconjS := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.S_maximal hyp.S_nonI
  have hnconjT := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp typeISetup.maximal ⟨typeISetup.typeI⟩
    hnconjS hnconjT
  have hone : r ∣ 1 := hcop ▸ Nat.dvd_gcd hrLF hrpq
  exact hr.one_lt.ne' (Nat.dvd_one.mp hone)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (13.19.b)**: `𝓛^{τ₁}` is orthogonal to the whole `η`-grid, for the honest
coherent extension `τ₁ = dataL.coh.extension`.  For `ψ ∈ 𝓛` (an enumerated `ζ_k`,
`exists_zeta_index_of_mem_Sset`), the conjugate partner `ζ_{k'} = ζ̄_k` is again a family
member (`exists_conjIndex_at`); `ζ_k^{τ₁} − ζ_{k'}^{τ₁}` is supported in `Ã(L)`
(`nu_zeta_sub_conj_support_at`), which avoids `Ŵ^G` by (13.19.a)
(`typeI_dadeSupport_avoids_regular`); the unit norms (`nu_zeta_norm_one`), conjugate
orthogonality (`nu_zeta_inner_nu_conj_eq_zero`), and `ℤ[Irr G]`-membership feed the (3.8)
rigidity engine `eta_orthogonal_of_norm_one_pair_vanish`. -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (dataL.coh.extension φ) (hyp.eta i j) = 0 := by
  classical
  have core : ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (hyp.eta i j) (dataL.coh.extension φ) = 0 := by
    obtain ⟨k, hk_ne, hkφ⟩ := exists_zeta_index_of_mem_Sset _hG dataL hφ
    have hk78 : k ≠ (dataL.h78 _hG).ind1H := by
      rw [dataL.h78_ind1H_eq]; exact hk_ne
    obtain ⟨k', hk'_ne, hk'⟩ := dataL.exists_conjIndex_at _hG hk_ne
    -- engine inputs from the coherence bundle
    have hpsiZ : (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k) ∈ ZIrr G := by
      rw [dataL.h78_nu_eq, dataL.h78_zeta_eq]
      exact dataL.coh.extension_mem_ZIrr _
        (Submodule.subset_span (dataL.zeta_mem_Sset hk_ne))
    have hconjZ : (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k') ∈ ZIrr G := by
      have hk'ne_data : k' ≠ dataL.ind1H := by
        rw [← dataL.h78_ind1H_eq _hG]; exact hk'_ne
      rw [dataL.h78_nu_eq, dataL.h78_zeta_eq]
      exact dataL.coh.extension_mem_ZIrr _
        (Submodule.subset_span (dataL.zeta_mem_Sset hk'ne_data))
    have hpsi1 := dataL.nu_zeta_norm_one _hG hk78
    have hconj1 := dataL.nu_zeta_norm_one _hG hk'_ne
    have hcross := dataL.nu_zeta_inner_nu_conj_eq_zero _hG _hG.odd hk_ne hk'_ne hk'
    have hsupp := dataL.nu_zeta_sub_conj_support_at _hG hk_ne hk'_ne hk'
    have havoid := typeI_dadeSupport_avoids_regular _hG hnoV hyp dataL.typeIHyp
    have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
        ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        ((dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k)
          - (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k')) x = 0 := by
      intro x hx
      by_contra hval
      have hxD := hsupp (ClassFunction.mem_support.mpr hval)
      rw [dataL.h78_hyp_eq] at hxD
      exact havoid x hx hxD
    intro i j
    have hengine := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
      hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
    have hid : (dataL.h78 _hG).nu ((dataL.h78 _hG).hyp76.zeta k)
        = dataL.coh.extension φ := by
      rw [dataL.h78_nu_eq, dataL.h78_zeta_eq, hkφ]
    rwa [hid] at hengine
  intro i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, core i j, star_zero]

end OddOrder.Peterfalvi.S15
