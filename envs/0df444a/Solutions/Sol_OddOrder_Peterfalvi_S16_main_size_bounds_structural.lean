-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.main_size_bounds_structural
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:27:03.9882+00:00
-- url     : https://prove2.me/submissions/ebdbc6e1-7e0c-4880-a932-50c478b1d5c3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/GroupTheory/CoprimeAction.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S15_ComplementStructure.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct
import Theorems.Thm_OddOrder_GroupTheory_isFrobenius_kernel_eq_bot_of_frobenius_subgroup
import Theorems.Thm_OddOrder_Isaacs_Ch06_IsFrobeniusGroup_conjComplement
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_isMulCommutative_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_u_le_cyclotomicQuotient
import Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
import Theorems.Thm_OddOrder_Peterfalvi_S16_card_modEq_one_of_prime_normalizing_fpf
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_side_caseB_facts
import Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_ratio_le

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

-- ===== OddOrder/GroupTheory/CoprimeAction.lean =====
namespace OddOrder.GroupTheory

section FrobeniusCentralizer

open OddOrder.Isaacs

variable {L : Type*} [Group L] [Finite L] {N A : Subgroup L}

/-- **A subgroup meeting the Frobenius kernel trivially is coprime to it.**  In a finite Frobenius
group with kernel `N` and complement `A`, if `K ⊓ N = ⊥` then `|K| ⟂ |N|`: `K` injects into the
quotient `L / N`, so `|K| ∣ [L : N] = |A|`, which is prime to `|N|`
(`coprime_card_kernel_complement`).  Reusable; supplies the `coprime_order` of the (9.1) action. -/
theorem IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot
    (h : Ch06.IsFrobeniusGroup L N A) {K : Subgroup L} (hKN : K ⊓ N = ⊥) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
  have := h.isNormal
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    exact Subtype.ext (Subgroup.disjoint_def.mp (disjoint_iff.mpr hKN) a.2 ha)
  have hdvd : Nat.card ↥K ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact Subgroup.card_dvd_of_injective _ hinj
  rw [h.isComplement.symm.index_eq_card] at hdvd
  exact Nat.Coprime.coprime_dvd_left hdvd h.coprime_card_kernel_complement.symm

/-- The ambient-`G` form of `coprime_card_of_inf_kernel_eq_bot`: for a Frobenius group `Lsub ≤ G`
with kernel `N` (`N ≤ Lsub`), a subgroup `K ≤ Lsub` meeting `N` trivially is coprime to `N`. -/
theorem IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le {G : Type*} [Group G] [Finite G]
    {Lsub N K : Subgroup G} {A : Subgroup ↥Lsub} (hNL : N ≤ Lsub) (hKL : K ≤ Lsub)
    (h : Ch06.IsFrobeniusGroup ↥Lsub (N.subgroupOf Lsub) A) (hKN : K ⊓ N = ⊥) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥N) := by
  have hsub : (K.subgroupOf Lsub) ⊓ (N.subgroupOf Lsub) = ⊥ := by
    rw [show K.subgroupOf Lsub ⊓ N.subgroupOf Lsub = (K ⊓ N).subgroupOf Lsub from
      (Subgroup.comap_inf K N Lsub.subtype).symm, hKN, Subgroup.bot_subgroupOf]
  have hcop := IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot h hsub
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv] at hcop

end FrobeniusCentralizer

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Frobenius-kernel self-centralizing (the gate-4 final step)**: in a finite Frobenius group `L`
with kernel `N`, any abelian subgroup `U` meeting `N` nontrivially lies in `N`.  Picking
`1 ≠ x ∈ U ⊓ N`, every `u ∈ U` commutes with `x` (`U` abelian), so `u ∈ C_L(x) ≤ N`
(`IsFrobeniusGroup.centralizer_kernel_le`: the centralizer of a nontrivial kernel element lies in
the kernel).  This is exactly the `U ⊆ C_L(U ∩ L_F) ⊆ L_F` deduction of Peterfalvi (13.17.b) once
`U ∩ L_F ≠ 1` is known.  General group theory; reusable, hoistable to `Ch06`. -/
theorem le_kernel_of_isMulCommutative_of_inf_ne_bot {L : Type*} [Group L] [Finite L]
    {N A U : Subgroup L} (h : Ch06.IsFrobeniusGroup L N A)
    (hUab : IsMulCommutative ↥U) (hinf : U ⊓ N ≠ ⊥) : U ≤ N := by
  obtain ⟨x, hxmem, hxne⟩ := (U ⊓ N).bot_or_exists_ne_one.resolve_left hinf
  have hxU : x ∈ U := (Subgroup.mem_inf.mp hxmem).1
  have hxN : x ∈ N := (Subgroup.mem_inf.mp hxmem).2
  have hcent := h.centralizer_kernel_le x hxN hxne
  intro u hu
  refine hcent (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  exact congrArg Subtype.val (hUab.is_comm.comm ⟨u, hu⟩ ⟨x, hxU⟩)

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

/-- **`T`-side dual of `typeI_U_le_fitting_of_coprime`** (Pf (13.17.b), V-side): for `T` type II and
a type-`I` maximal `L` over `N_G(V)` with `|L_F| ⟂ pq`, the complement `V ⊆ L_F`.  Mirror of the
`U`-side; the `V W₂` Frobenius is built from the reconciled `TypePData T`
(`typeP_uW1_frobenius`) rather than `basic_structure` (which is `S`-side only). -/
theorem typeI_V_le_fitting_of_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L)
    (hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q)) :
    hyp.V ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
  obtain ⟨frob, _⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hLmax hLI
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hfrobLF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((maxNilpotentNormalHall L).subgroupOf L) frob.complement := hHeq ▸ frob.frobenius
  have hVleL : hyp.V ≤ L := Subgroup.le_normalizer.trans hNVL
  have hW2leL : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  have hLFleL : maxNilpotentNormalHall L ≤ L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  have hsolv : Group.IsSolvable ↥(maxNilpotentNormalHall L) := by
    have := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent L
    exact IsNilpotent.to_isSolvable
  have hcopLFp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hW2LF : hyp.W2 ⊓ maxNilpotentNormalHall L = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [← hyp.p_eq_card_W2]; exact hcopLFp.symm)).eq_bot
  have hVmeets : hyp.V ⊓ maxNilpotentNormalHall L ≠ ⊥ := by
    intro hbot
    have hcopV : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hVleL hfrobLF hbot
    have hcopW2 : Nat.Coprime (Nat.card ↥hyp.W2) (Nat.card ↥(maxNilpotentNormalHall L)) :=
      OddOrder.GroupTheory.IsFrobeniusGroup.coprime_card_of_inf_kernel_eq_bot_le
        hLFleL hW2leL hfrobLF hW2LF
    have hcardVW2 : Nat.card ↥(hyp.V ⊔ hyp.W2) = Nat.card ↥hyp.V * Nat.card ↥hyp.W2 := by
      rw [← hVW2frob.isComplement.card_mul_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    have hcopVW2 : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L))
        (Nat.card ↥(hyp.V ⊔ hyp.W2)) := by
      rw [hcardVW2]; exact Nat.Coprime.mul_right hcopV.symm hcopW2.symm
    have hLFbot : maxNilpotentNormalHall L = ⊥ :=
      OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup hLFleL
        (sup_le hVleL hW2leL) ⟨frob.complement, hfrobLF⟩ hVW2frob hbot hW2LF hsolv hcopVW2
    exact frob.frobenius.ne_bot_kernel (by rw [hHeq, hLFbot, Subgroup.bot_subgroupOf])
  have hVab : IsMulCommutative ↥(hyp.V.subgroupOf L) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hVleL).symm (isMulCommutative_V hG hyp ⟨tdata⟩)
  have hinf : (hyp.V.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L) ≠ ⊥ := by
    rw [show (hyp.V.subgroupOf L) ⊓ ((maxNilpotentNormalHall L).subgroupOf L)
        = (hyp.V ⊓ maxNilpotentNormalHall L).subgroupOf L from (Subgroup.comap_inf _ _ _).symm]
    intro h
    apply hVmeets
    have hle : hyp.V ⊓ maxNilpotentNormalHall L ≤ L := inf_le_right.trans hLFleL
    rw [← inf_eq_left.mpr hle]
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  have hsub := le_kernel_of_isMulCommutative_of_inf_ne_bot hfrobLF hVab hinf
  calc hyp.V = (hyp.V.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hVleL).symm
    _ ≤ ((maxNilpotentNormalHall L).subgroupOf L).map L.subtype := Subgroup.map_mono hsub
    _ = maxNilpotentNormalHall L := Subgroup.map_subgroupOf_eq_of_le hLFleL

/-- **`T`-side dual of `typeI_overNormalizer_U_le_fitting`** (Pf (13.17.b), V-side): for `T` type II
and a type-`I` maximal `L` over `N_G(V)`, `V ⊆ L_F`.  Mirror; cites the (8.17.a) coprimality
`card_LF_coprime_pq` (gated, BG Thm E) and the V-side FPF residual
`typeI_V_le_fitting_of_coprime`. -/
theorem typeI_overNormalizer_V_le_fitting [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    hyp.V ≤ maxNilpotentNormalHall L := by
  have hnS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  exact typeI_V_le_fitting_of_coprime _hG hnoV hyp hTTypeII hLmax hLI hNVL
    (card_LF_coprime_pq _hG hyp hLmax hLI hnS hnT)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_ComplementStructure.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`T`-side dual of `q_not_dvd_kernel`** (V-side): `p = |W₂|` is coprime to the type-I Frobenius
kernel `L_F` (`p ∤ |L_F|`).  Mirror; same gated input `card_LF_coprime_pq` (`|L_F| ⟂ pq`). -/
theorem p_not_dvd_kernel [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L) :
    ¬ hyp.p ∣ Nat.card ↥(frob.typeI.typeF.H.subgroupOf L) := by
  have hnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.S_maximal hyp.S_nonI
  have hnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T :=
    not_conj_of_isTypeI_of_isTypeNonI _hG hLI hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp hLmax hLI hnconjS hnconjT
  have hcopp : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) hyp.p :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right hyp.p hyp.q) hcop
  have hnotdvd : ¬ hyp.p ∣ Nat.card ↥(maxNilpotentNormalHall L) :=
    hyp.p_prime.coprime_iff_not_dvd.mp hcopp.symm
  have hHeq : frob.typeI.typeF.H = maxNilpotentNormalHall L := frob.typeI.typeF.H_eq
  have hHleL : frob.typeI.typeF.H ≤ L := by
    rw [hHeq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleL).toEquiv, hHeq]
  exact hnotdvd

/-- **`T`-side dual of `exists_typeIFrobeniusData_W1_le`** (V-side): the type-I Frobenius
decomposition of `L` can be taken with the complement containing `W₂` (`|W₂| = p` coprime to the
kernel by `p_not_dvd_kernel`, Schur–Zassenhaus complement conjugacy). -/
theorem exists_typeIFrobeniusData_W2_le [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLtypeI : IsTypeI L) (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    ∃ frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L, frob.kernel_eq_MF ∧
      hyp.W2 ≤ frob.complement.map L.subtype := by
  obtain ⟨frob₀, hker₀⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV hLmax hLtypeI
  have hW2L : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  have : (frob₀.typeI.typeF.H.subgroupOf L).Normal := frob₀.frobenius.isNormal
  have hLsolv : Group.IsSolvable ↥L :=
    _hG.isSolvable_of_lt_top L (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hLmax).1)
  have : Group.IsSolvable ↥(frob₀.typeI.typeF.H.subgroupOf L) := inferInstance
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W2.subgroupOf L))
      (Nat.card ↥(frob₀.typeI.typeF.H.subgroupOf L)) := by
    have hW2card : Nat.card ↥(hyp.W2.subgroupOf L) = hyp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2L).toEquiv]
      exact hyp.p_eq_card_W2.symm
    rw [hW2card]
    exact (hyp.p_prime.coprime_iff_not_dvd).mpr (p_not_dvd_kernel _hG hyp hLmax hLtypeI frob₀)
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    inferInstance frob₀.frobenius.isComplement hcop
  refine ⟨{ frob₀ with
      complement := frob₀.complement.map (MulAut.conj x).toMonoidHom
      frobenius := frob₀.frobenius.conjComplement x }, frob₀.kernel_eq_MF_holds, ?_⟩
  have : hyp.W2 = (hyp.W2.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le hW2L]
  rw [this]
  exact Subgroup.map_mono hx

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeII.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.12), `T`-side `d = 1` in the Section 16 context** (issue 9077):
`V ⊓ C_G(Q) = ⊥`.  The honest (13.4) character-degree producer supplies `D = ⊥`, and the
canonical identity `D = V ⊓ C_G(Q)` turns it into the faithful-action statement.  This downstream
placement avoids the genuine import cycle from `S15_SAndTBasic` to the character-degree layer. -/
theorem Hypothesis.V_inf_centralizer_Q_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.base.V ⊓ Subgroup.centralizer (hyp.base.Q : Set G) = ⊥ := by
  rw [← hyp.base.D_eq]
  exact (T_side_caseB_facts hG hyp).1

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion** — the deep content of the type
determination, now discharged.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`,
consumed at `PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via
the character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.

Formalised as the universal (11.9.c) Type-IV exclusion `not_isTypeIV_of_mem_maximalSubgroups`
(`S13_NonGaloisExclusion`, sorry-free): the `IsMulCommutative V` residual that used to live here
follows from `cyclic V ⟸ typeP_Galois T`, whose full §5–§13 chain
(`not_isTypeIV_of_hypothesis`/`U_isCyclic_of_hypothesis`) is landed.  The direct cite became
possible once the §12–16 import inversion (issue 9093) removed `S13_NonGaloisExclusion`'s
transitive dependency on §16. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (_hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T :=
  OddOrder.Peterfalvi.S13.not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type
III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by the (10.10)
hypothesis `hnoV` (instantiate with the axiom-clean `no_typeV_maximal_unconditional`,
`S12_Noncoherence`; issue 9087), so `M_F ≠ M_σ` and `T` is Type III or IV. Excluding Type IV — the
genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the
III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by the (10.10) hypothesis `hnoV`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    hnoV ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual.**  Starting from the symmetric
(13.1) non-type-I carrier, `T` is sharpened to BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from
`T_nonI` (`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8): its
pure cyclotomic comparison lives upstream in `KeyInequalityArithmetic`, while the two
group-theoretic
order inputs are the direct (13.4) producer `T_side_caseB_facts` and the (13.15) producer
`Hypothesis.u_le_cyclotomicQuotient`.  Thus no forward reference through the later
`key_inequality` theorem is needed. -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hnoV hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) :=
    T_typeIII_ratio_le hG hnoV hncH0C hyp hIII
  -- The arithmetic half of (14.8), separated from the later `key_inequality` packaging.
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  -- Its T-side order input is the direct (13.4) producer, which is upstream of `T_isTypeP2`.
  have hvfull := (T_side_caseB_facts hG hyp).2
  -- The required S-side upper bound is the unconditional cyclotomic quotient estimate.
  have hu_le_full :
      hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    hyp.base.u_le_cyclotomicQuotient hG
  have hqpos : (0 : ℚ) < hyp.base.q := by
    exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right hu_le_full 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    rw [hvfull]
    exact lt_of_le_of_lt hu_div hratio
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  `T` is of type `P₂`
(`T_isTypeP2`), and *every* type-`P₂` maximal subgroup is type II by the proven BG bridge
`isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact
`T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hnoV hncH0C hyp)

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **A Frobenius complement acts fixed-point-freely on its kernel** (ambient-group form).
If `↥L` is a Frobenius group with kernel `H.subgroupOf L` and complement `compl`, and `H ≤ L`,
then every `a ≠ 1` lying — as a `G`-element — in the complement image `compl.map L.subtype`
conjugates no nontrivial `u ∈ H` to itself: `a * u * a⁻¹ ≠ u`.  This transports
`IsFrobeniusGroup.conj_frobenius` from `↥L` down to `G` through `L.subtype`. -/
theorem isFrobeniusGroup_conj_ne_of_mem_map_complement
    {L H : Subgroup G} {compl : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L (H.subgroupOf L) compl)
    (hHL : H ≤ L) {a : G} (ha_mem : a ∈ compl.map L.subtype) (ha_ne : a ≠ 1)
    {u : G} (hu_mem : u ∈ H) (hu_ne : u ≠ 1) :
    a * u * a⁻¹ ≠ u := by
  obtain ⟨a', ha'_compl, ha'_eq⟩ := Subgroup.mem_map.mp ha_mem
  have ha'_ne : a' ≠ 1 := by
    intro h
    rw [h] at ha'_eq
    exact ha_ne (by simpa using ha'_eq.symm)
  have hmemL : u ∈ L := hHL hu_mem
  have hu'_ker : (⟨u, hmemL⟩ : ↥L) ∈ H.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]; exact hu_mem
  have hu'_ne : (⟨u, hmemL⟩ : ↥L) ≠ 1 := fun h => hu_ne (congrArg Subtype.val h)
  have hconj := hfrob.conj_frobenius a' ha'_compl ha'_ne ⟨u, hmemL⟩ hu'_ker hu'_ne
  intro hcontra
  apply hconj
  apply Subtype.coe_injective
  change ((a' * ⟨u, hmemL⟩ * a'⁻¹ : ↥L) : G) = ((⟨u, hmemL⟩ : ↥L) : G)
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, InvMemClass.coe_inv,
    show ((a' : G)) = a from ha'_eq]
  exact hcontra

/-- If `x ≡ 1 (mod p)` with `p` odd and `≥ 2`, `x` odd and `x ≠ 1`, then `x ≥ 2p + 1`.  This is the
elided "fixed-point-free congruence + oddness" step of Peterfalvi (14.11.1): `x ≡ 1 (mod p)` and
`x ≠ 1` give `x = pm + 1` with `m ≥ 1`, and `x` odd with `p` odd forces `m` even, hence `m ≥ 2`. -/
private theorem two_mul_add_one_le_of_modEq_one_odd {p x : ℕ} (hp : Odd p) (hp2 : 2 ≤ p)
    (hmod : x ≡ 1 [MOD p]) (hodd : Odd x) (hne : x ≠ 1) : 2 * p + 1 ≤ x := by
  have hxmod : x % p = 1 := by
    have h := hmod
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (by omega : 1 < p)] at h
  have hdm := Nat.div_add_mod x p
  set m := x / p with hm_def
  rw [hxmod] at hdm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hdm; omega
    · exact h1
  have hpm_even : Even (p * m) := by
    rcases hodd with ⟨t, ht⟩; exact ⟨t, by omega⟩
  have hm_even : Even m := by
    by_contra hodd_m
    rw [Nat.not_even_iff_odd] at hodd_m
    exact (Nat.not_odd_iff_even.mpr hpm_even) (Nat.odd_mul.mpr ⟨hp, hodd_m⟩)
  have hm2 : 2 ≤ m := by rcases hm_even with ⟨r, hr⟩; omega
  have hpm : 2 * p ≤ p * m := by
    calc 2 * p = p * 2 := by ring
      _ ≤ p * m := by gcongr
  omega

/-- **Peterfalvi (14.11.1)** structural half: under `K ≠ V`, the Fitting kernel `K = M_F` is large
(`k > 2 p v`) and `(k − 1) / e > (v − 1) / p`.  The strict quotient bound is a genuine
consequence of `k > 2 p v`, `e ≤ p q`, and `q < p`: cross multiplication reduces it to
`e(v−1) ≤ pq(v−1) < p(k−1)`.  The `k > 2 p v` bound is in turn
the arithmetic consequence (`two_mul_add_one_le_of_modEq_one_odd`) of the §13/§15 structural datum
`hstruct` of (14.11.1): by (13.17) the kernel order factors as `k = v·x` with `x` an integer,
`x ≠ 1`
(as `K ≠ V`), and `x ≡ 1 (mod p)` (since `W₂` acts fixed-point-freely on `K` and `V`); as `k = |K|`
is odd, `x` is odd, so `x ≥ 2p+1` and `k = vx > 2pv`.  The third inequality of (14.11.1),
`(v − 1) / p > (u − 1) / q`, is `key_ratio_inequality_of_caseB_data` (14.8), discharged in
`main_size_bounds`. -/
theorem _root_.solution [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V)
    (he_le : Mdata.e ≤ hyp.base.p * hyp.base.q) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) := by
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  -- (14.11.1): `k = v·x`, `x ≡ 1 (mod p)` (`W₂` fixed-point-free on `K`, `V`), `x ≠ 1` (`K ≠ V`) —
  -- the §13/§15 structural datum (13.17); `k > 2 p v` is then arithmetic (`x` odd, so `x ≥ 2p+1`).
  have hstruct : ∃ x : ℕ, Mdata.k = hyp.base.v * x ∧ x ≡ 1 [MOD hyp.base.p] ∧ x ≠ 1 := by
    have hMI : IsTypeI Mdata.M := ⟨Mdata.typeIHyp.typeI⟩
    have hTII : IsTypeII hyp.base.T := T_typeII _hG hnoV hncH0C hyp
    -- **(13.17)/(14.11.1)**: `V ≤ K = M_F` (type-I-over-`N_G(V)` Fitting inclusion).
    have hVK : hyp.base.V ≤ Mdata.K := by
      rw [Mdata.K_eq_MF]
      exact OddOrder.Peterfalvi.S15.typeI_overNormalizer_V_le_fitting _hG hnoV hyp.base hTII
        Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    -- `|V| = v` (`d = 1` from `D = V ⊓ C_G(Q) = ⊥`, (13.12) dual).
    have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
      have hDbot : hyp.base.D = ⊥ := by
        rw [hyp.base.D_eq]
        exact hyp.V_inf_centralizer_Q_eq_bot _hG
      have hd1 : hyp.base.d = 1 := by rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
      rw [hyp.base.card_V_eq_vd, hd1, mul_one]
    -- `v ∣ k` from `V ≤ K`; set `x = k / v`.
    have hvdvdk : hyp.base.v ∣ Mdata.k := by
      rw [Mdata.k_eq_card_K, ← hVcard]
      exact Subgroup.card_dvd_of_le hVK
    obtain ⟨x, hkx⟩ := hvdvdk
    -- **(13.17)**: type-I Frobenius data with `W₂ ≤ complement`, so `W₂` acts fpf on `K = M_F`.
    obtain ⟨frob, _hker, hW2E⟩ := OddOrder.Peterfalvi.S15.exists_typeIFrobeniusData_W2_le
      _hG hnoV hyp.base Mdata.M_maximal hMI Mdata.normalizer_V_le_M
    have hKeq : Mdata.K = frob.typeI.typeF.H := by rw [Mdata.K_eq_MF, frob.typeI.typeF.H_eq]
    have hW2card : Nat.card ↥hyp.base.W2 = hyp.base.p := hyp.base.p_eq_card_W2.symm
    have hW2M : hyp.base.W2 ≤ Mdata.M := by
      intro a ha
      obtain ⟨x', _, hx'⟩ := Subgroup.mem_map.mp (hW2E ha)
      rw [← hx']; exact x'.2
    have hW2normK : hyp.base.W2 ≤ Subgroup.normalizer (Mdata.K : Set G) := by
      refine hW2M.trans ?_
      rw [Mdata.K_eq_MF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer Mdata.M
    -- `W₂` acts fixed-point-freely on `K` (Frobenius complement on the kernel).
    have hfpfK : ∀ a ∈ hyp.base.W2, a ≠ 1 → ∀ u ∈ Mdata.K, u ≠ 1 → a * u * a⁻¹ ≠ u := by
      intro a ha ha_ne u hu hu_ne
      refine isFrobeniusGroup_conj_ne_of_mem_map_complement frob.frobenius
        frob.typeI.typeF.H_le (hW2E ha) ha_ne ?_ hu_ne
      rw [← hKeq]; exact hu
    -- `k ≡ 1 (mod p)` and `v ≡ 1 (mod p)` (`W₂` fpf on `K` and on `V ≤ K`).
    have hkmod : Mdata.k ≡ 1 [MOD hyp.base.p] := by
      rw [Mdata.k_eq_card_K]
      exact card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2card hW2normK hfpfK
    have hvmod : hyp.base.v ≡ 1 [MOD hyp.base.p] := by
      rw [← hVcard]
      refine card_modEq_one_of_prime_normalizing_fpf hyp.base.p_prime hW2card
        hyp.base.W2_normalizes_V ?_
      intro a ha ha_ne u hu hu_ne
      exact hfpfK a ha ha_ne u (hVK hu) hu_ne
    refine ⟨x, hkx, ?_, ?_⟩
    · -- `x ≡ 1 (mod p)`: from `v x = k ≡ 1` and `v ≡ 1`.
      have hvx1 : hyp.base.v * x ≡ 1 [MOD hyp.base.p] := hkx ▸ hkmod
      have hvxx : hyp.base.v * x ≡ x [MOD hyp.base.p] := by simpa using hvmod.mul_right x
      exact hvxx.symm.trans hvx1
    · -- `x ≠ 1`: if `x = 1` then `k = v`, so `|K| = |V|` with `V ≤ K`, forcing `V = K` (⊥ `K ≠ V`).
      intro hx1
      have hkv : Mdata.k = hyp.base.v := by rw [hkx, hx1, Nat.mul_one]
      have hKcardV : Nat.card ↥Mdata.K = Nat.card ↥hyp.base.V := by
        rw [← Mdata.k_eq_card_K, hkv, hVcard]
      exact hne (Subgroup.eq_of_le_of_card_ge hVK (le_of_eq hKcardV)).symm
  have hk : Mdata.k > 2 * hyp.base.p * hyp.base.v := by
    obtain ⟨x, hkx, hxmod, hxne⟩ := hstruct
    have hk_odd : Odd Mdata.k := by
      rw [Mdata.k_eq_card_K]
      exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Mdata.K)
    have hvx_odd : Odd (hyp.base.v * x) := hkx ▸ hk_odd
    have hx_odd : Odd x := (Nat.odd_mul.mp hvx_odd).2
    have hv_pos : 0 < hyp.base.v := by rcases (Nat.odd_mul.mp hvx_odd).1 with ⟨r, hr⟩; omega
    have hx_ge : 2 * hyp.base.p + 1 ≤ x :=
      two_mul_add_one_le_of_modEq_one_odd hyp.base.p_odd hyp.base.p_prime.two_le hxmod hx_odd hxne
    have hle : hyp.base.v * (2 * hyp.base.p + 1) ≤ hyp.base.v * x := by gcongr
    have hexpand : hyp.base.v * (2 * hyp.base.p + 1)
        = 2 * hyp.base.p * hyp.base.v + hyp.base.v := by ring
    rw [hkx]; omega
  refine ⟨hk, ?_⟩
  -- The strict quotient bound `(k−1)/e > (v−1)/p` is pure arithmetic from `k > 2pv`, `q < p`,
  -- and the faithful (13.17.c)-dual bound `e ≤ pq`:
  -- `e(v−1) ≤ pq(v−1) = p·q(v−1) ≤ p(k−1)`.
  have hv_pos : 0 < hyp.base.v := by
    obtain ⟨x, hkx, _, _⟩ := hstruct
    have hk_odd : Odd Mdata.k := by
      rw [Mdata.k_eq_card_K]
      exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Mdata.K)
    have hvx_odd : Odd (hyp.base.v * x) := hkx ▸ hk_odd
    exact (Nat.odd_mul.mp hvx_odd).1.pos
  have hNat : hyp.base.q * (hyp.base.v - 1) < Mdata.k - 1 := by
    have hb : 2 * hyp.base.p * hyp.base.v ≤ Mdata.k - 1 := Nat.le_sub_one_of_lt hk
    have ha : hyp.base.q * (hyp.base.v - 1) < 2 * hyp.base.p * hyp.base.v := by
      calc hyp.base.q * (hyp.base.v - 1) ≤ hyp.base.q * hyp.base.v := by gcongr; omega
        _ < 2 * hyp.base.p * hyp.base.v := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) hv_pos
    exact lt_of_lt_of_le ha hb
  rw [gt_iff_lt]
  have hppos : (0 : ℚ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have heposNat : 0 < Mdata.e := by
    rw [Mdata.e_eq_index]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hepos : (0 : ℚ) < Mdata.e := by exact_mod_cast heposNat
  rw [div_lt_div_iff₀ hppos hepos]
  have hcross :
      (hyp.base.v - 1) * Mdata.e < (Mdata.k - 1) * hyp.base.p := by
    calc
      (hyp.base.v - 1) * Mdata.e
          ≤ (hyp.base.v - 1) * (hyp.base.p * hyp.base.q) := by gcongr
      _ = hyp.base.p * (hyp.base.q * (hyp.base.v - 1)) := by ring
      _ < hyp.base.p * (Mdata.k - 1) := by
        exact Nat.mul_lt_mul_of_pos_left hNat hyp.base.p_prime.pos
      _ = (Mdata.k - 1) * hyp.base.p := by ring
  exact_mod_cast hcross

end OddOrder.Peterfalvi.S16
