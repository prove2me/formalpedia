-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.exists_typeI_maximal_overNormalizer_V
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:34.409765+00:00
-- url     : https://prove2.me/submissions/7622dce1-3d8b-43e1-89fc-eb0fc18c7e9d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/GroupTheory/CoprimeAction.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct
import Theorems.Thm_OddOrder_GroupTheory_isFrobenius_kernel_eq_bot_of_frobenius_subgroup
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_V_card_Q_of_disjoint
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_conj_typeP_V_of_coprime
import Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_le_of_isHall_subgroupOf_of_conj
import Theorems.Thm_OddOrder_Peterfalvi_S15_isMulCommutative_V

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

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`T`-side dual of `not_normalizer_U_le_S`** (Pf (13.17), V-side): if `V` is a `T`-conjugate of
the `TypeIIData` witness's complement `tdata.typeP.U`, then `N_G(V) ⊄ T`.  Transfers the type-II
property `tdata.normalizer_not_le` along the conjugation `V = (typeP.U)^x`, `x ∈ T`. -/
theorem not_normalizer_V_le_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (tdata : TypeIIData hyp.T)
    (hconj : ∃ x : G, x ∈ hyp.T ∧ hyp.V = MulAut.conj x • tdata.typeP.U) :
    ¬ Subgroup.normalizer (hyp.V : Set G) ≤ hyp.T := by
  obtain ⟨x, hxT, hVconj⟩ := hconj
  intro hNVT
  refine tdata.normalizer_not_le ?_
  have hTfix : MulAut.conj x • hyp.T = hyp.T :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxT)
  have hnorm_eq : Subgroup.normalizer (hyp.V : Set G)
      = MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G) := by
    rw [hVconj]
    exact (OddOrder.BG.Ch3.S12.normalizer_conj_smul x tdata.typeP.U).symm
  rw [hnorm_eq] at hNVT
  have hle : MulAut.conj x • Subgroup.normalizer ((tdata.typeP.U : Subgroup G) : Set G)
      ≤ MulAut.conj x • hyp.T := by rw [hTfix]; exact hNVT
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hle

/-- A subgroup `H ≤ V` whose order is coprime to its index `[V : H]` is a Hall subgroup of `V`
for `π = π(|H|)` (its own set of prime divisors).  The Hall conditions are immediate:
`π(|H|) ⊆ π` by definition, and no prime of `[V : H]` divides `|H|`, by coprimality. -/
theorem isHall_subgroupOf_primeFactors_of_coprime_index [Finite G] {V H : Subgroup G}
    (hHV : H ≤ V) (hcop : Nat.Coprime (Nat.card ↥H) ((H.subgroupOf V).index)) :
    Ch03.IsHallSubgroup {p | p ∈ (Nat.card ↥H).primeFactors} (H.subgroupOf V) := by
  have hcard : Nat.card ↥(H.subgroupOf V) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHV).toEquiv
  refine ⟨fun p hp => by rw [hcard] at hp; exact hp, fun p hp hpπ => ?_⟩
  rw [Nat.mem_primeFactors] at hp
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hpπ).2.1 hp.2.1
  exact absurd (Nat.dvd_one.mp hp1) hp.1.ne_one

end OddOrder.Peterfalvi.S15

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

/-- **`S`-side dual of `tConjugate_fitting_data`** (Pf (13.17.a), V-side L~S exclusion input): for a
maximal `L` conjugate to `S`, the Fitting kernel `L_F` is a `p`-group of order `p^q` containing `W₂`
and meeting `V` trivially.  **Now proven** (the V-side mirror of `tConjugate_fitting_data`): part
(1)
`|L_F| = p^q` from the proven `card_P_eq` via the `S`-conjugation equivariance of `M_F`; part (2)
`W₂ ≤ L_F` places the `p`-group `W₂ ⊆ N_G(V) ⊆ L` in the normal `p`-Hall `L_F`; part (3)
`L_F ⊓ V = ⊥`
from `|L_F| = p^q` coprime to `|V|` (`V ⋊ W₂` Frobenius, `(|V|, p) = 1`).  `IsTypeII T` (for the
`V ⋊ W₂` Frobenius) is threaded from `exists_typeI_maximal_overNormalizer_V`. -/
theorem sConjugate_fitting_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    {L : Subgroup G} {g : G} (hconj : MulAut.conj g • L = hyp.S)
    (hNVL : Subgroup.normalizer (hyp.V : Set G) ≤ L) :
    Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q ∧
      hyp.W2 ≤ maxNilpotentNormalHall L ∧
      maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := by
  -- part 1: `|L_F| = p^q` (`card_P_eq`, proven, via the `S`-conjugation equivariance of `M_F`).
  have hLFcard : Nat.card ↥(maxNilpotentNormalHall L) = hyp.p ^ hyp.q := by
    have hMF : MulAut.conj g • maxNilpotentNormalHall L = hyp.P := by
      rw [maxNilpotentNormalHall_pointwise_smul, hconj, ← hyp.P_eq_SF]
    have hcard : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.P := by
      rw [← hMF]
      exact Nat.card_congr
        (Subgroup.equivSMul (MulAut.conj g) (maxNilpotentNormalHall L)).toEquiv
    rw [hcard]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `W₂ ⊆ N_G(V) ⊆ L`.
  have hW2leL : hyp.W2 ≤ L := hyp.W2_normalizes_V.trans hNVL
  -- part 2: `W₂ ≤ L_F` — `W₂` a `p`-group in `L`, `L_F` the normal `p`-Hall subgroup.
  have hW2leLF : hyp.W2 ≤ maxNilpotentNormalHall L := by
    refine pgroup_le_of_normal_coprime_index (S := L) hyp.p_prime hW2leL
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L) ?_ ?_ ?_
    · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard_eq : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
    · rw [hLFcard]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
    · intro w hw
      have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
        (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
      have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
      rw [heq, ← hyp.p_eq_card_W2] at h1
      exact h1
  -- part 3: `L_F ⊓ V = ⊥` — `|L_F| = p^q` coprime to `|V|` (`V ⋊ W₂` Frobenius gives
  -- `(|V|, p) = 1`).
  have hLFV : maxNilpotentNormalHall L ⊓ hyp.V = ⊥ := by
    obtain ⟨tpd, htpdV, htpdW1, _⟩ := reconciled_typePData_T hG hyp
    obtain ⟨tdata⟩ := hTTypeII
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
      rwa [htpdV, htpdW1] at h
    have hcopVp : Nat.Coprime (Nat.card ↥hyp.V) hyp.p := by
      have hk := hVW2frob.coprime_card_kernel_complement
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
        ← hyp.p_eq_card_W2] at hk
      exact hk
    have hcop : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥hyp.V) := by
      rw [hLFcard]; exact hcopVp.symm.pow_left hyp.q
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  exact ⟨hLFcard, hW2leLF, hLFV⟩

/-- **`T`-side dual of `exists_typeI_maximal_overNormalizer_U`** (Pf (13.17.a/b), V-side): for `T`
type II, a maximal subgroup `L` over `N_G(V)` is type I with `V ⊆ L_F`.  Mirror of the `U`-side with
the two exclusion branches swapped: `L ~ T` is ruled out by the Hall conjugacy `N_G(V) ⊄ T`
(`not_normalizer_V_le_T`), and `L ~ S` by the `|L_F| = p^q` order contradiction
(`sConjugate_fitting_data`) against the `V W₂` Frobenius (from the reconciled `TypePData T`). -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ IsTypeI L ∧
      Subgroup.normalizer (hyp.V : Set G) ≤ L ∧ hyp.V ≤ maxNilpotentNormalHall L := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T _hG hyp
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
  have hcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q) :=
    coprime_card_V_card_Q_of_disjoint hyp tdata hdisj
  have hNVT : ¬ Subgroup.normalizer (hyp.V : Set G) ≤ hyp.T :=
    not_normalizer_V_le_T _hG hyp tdata (exists_conj_typeP_V_of_coprime _hG hyp tdata hcop)
  have hVne : hyp.V ≠ ⊥ := by
    obtain ⟨x, _, hVconj⟩ := exists_conj_typeP_V_of_coprime _hG hyp tdata hcop
    rw [hVconj]
    exact mt (pointwise_smul_eq_bot_iff (MulAut.conj x)).mp tdata.common.1
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hVleT : hyp.V ≤ hyp.T := (le_sup_right.trans hyp.T_deriv_eq_QV.ge).trans hM'_le_T
  have hVneTop : hyp.V ≠ ⊤ := fun hVtop =>
    (mem_maximalSubgroups.mp hyp.T_maximal).1 (top_le_iff.mp (hVtop ▸ hVleT))
  have hNVtop : Subgroup.normalizer (hyp.V : Set G) ≠ ⊤ := by
    intro hNtop
    have hVnormal : (hyp.V).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases _hG.simple.eq_bot_or_eq_top_of_normal hyp.V hVnormal with h | h
    · exact hVne h
    · exact hVneTop h
  obtain ⟨L, hNVL, hLmaximal⟩ :=
    Finite.exists_le_maximal (p := fun K : Subgroup G => K ≠ ⊤) hNVtop
  have hLmem : L ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr ⟨hLmaximal.1, fun b hLb => by
      by_contra hbne
      exact lt_irrefl L (lt_of_lt_of_le hLb (hLmaximal.2 hbne hLb.le))⟩
  -- `V W₂` Frobenius from the reconciled `TypePData T` (used by both exclusion branches).
  have htpdVne : tpd.U ≠ ⊥ := by rw [htpdV]; exact hVne
  have hVW2frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  rcases hyp.theorem88_caseB L hLmem with hLI | hLconjS | hLconjT
  · exact ⟨L, hLmem, hLI, hNVL,
      typeI_overNormalizer_V_le_fitting _hG hnoV hyp ⟨tdata⟩ hLmem hLI hNVL⟩
  · -- `L ~ S` excluded (order contradiction, mirror of the S-side `L ~ T`).
    exfalso
    obtain ⟨g, hg⟩ := hLconjS
    obtain ⟨_hLFcard, hW2le, hLFV⟩ := sConjugate_fitting_data _hG hyp ⟨tdata⟩ hg hNVL
    have hVleL : hyp.V ≤ L := Subgroup.le_normalizer.trans hNVL
    have hV_norm_LF : hyp.V ≤ Subgroup.normalizer (maxNilpotentNormalHall L) :=
      hVleL.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L)
    have hVW2_le_V : ⁅hyp.V, hyp.W2⁆ ≤ hyp.V :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hyp.W2_normalizes_V
    have hVW2_le_LF : ⁅hyp.V, hyp.W2⁆ ≤ maxNilpotentNormalHall L := by
      refine (Subgroup.commutator_mono (le_refl hyp.V) hW2le).trans ?_
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hV_norm_LF
    have hVW2_bot : ⁅hyp.V, hyp.W2⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hVW2_le_LF hVW2_le_V).trans hLFV.le)
    have hVcent : hyp.V ≤ Subgroup.centralizer (hyp.W2 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVW2_bot
    have hW2ne : hyp.W2 ≠ ⊥ := by
      intro hbot
      have : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
      exact hyp.p_prime.one_lt.ne' this
    obtain ⟨w, hwW2, hwne⟩ := (hyp.W2.bot_or_exists_ne_one).resolve_left hW2ne
    obtain ⟨n, hnV, hnne⟩ := (hyp.V.bot_or_exists_ne_one).resolve_left hVne
    have hcomm : w * n * w⁻¹ = n := by
      have := hVcent hnV w hwW2
      rw [mul_inv_eq_iff_eq_mul, this]
    have hwVW2 : w ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_right hwW2
    have hnVW2 : n ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_left hnV
    have hwmem : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2) := hwW2
    have hnmem : (⟨n, hnVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.V.subgroupOf (hyp.V ⊔ hyp.W2) := hnV
    have hwne' : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 := fun h => hwne (congrArg Subtype.val h)
    have hnne' : (⟨n, hnVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 := fun h => hnne (congrArg Subtype.val h)
    have hconj_eq : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) * ⟨n, hnVW2⟩ * ⟨w, hwVW2⟩⁻¹ = ⟨n, hnVW2⟩ :=
      Subtype.ext (by simpa using hcomm)
    exact hVW2frob.conj_frobenius _ hwmem hwne' _ hnmem hnne' hconj_eq
  · -- `L ~ T` excluded (Hall conjugacy, mirror of the S-side `L ~ S`): `N_G(V) ⊆ T` vs `hNVT`.
    obtain ⟨g, hg⟩ := hLconjT
    have hVhall_cop : Nat.Coprime (Nat.card ↥hyp.V) ((hyp.V.subgroupOf hyp.T).index) := by
      have frobcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.W2) := by
        have h := hVW2frob.coprime_card_kernel_complement
        rwa [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_left : hyp.V ≤ hyp.V ⊔ hyp.W2)).toEquiv,
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (le_sup_right : hyp.W2 ≤ hyp.V ⊔ hyp.W2)).toEquiv] at h
      have hQleM' : hyp.Q ≤ derivedInG hyp.T := le_sup_left.trans hyp.T_deriv_eq_QV.ge
      have hidxM' : ((derivedInG hyp.T).subgroupOf hyp.T).index = Nat.card ↥hyp.W2 := by
        rw [← htpdW2, ← tpd.card_W1_eq_derived_index]
      have hidxQ : (hyp.Q.subgroupOf (derivedInG hyp.T)).index = Nat.card ↥hyp.V := by
        rw [hyp.Q_eq_TF, ← tpd.card_U_eq_index, htpdV]
      have hTcard : Nat.card ↥hyp.T
          = Nat.card ↥hyp.W2 * (Nat.card ↥hyp.V * Nat.card ↥hyp.Q) := by
        have e1 := ((derivedInG hyp.T).subgroupOf hyp.T).index_mul_card
        have e2 := (hyp.Q.subgroupOf (derivedInG hyp.T)).index_mul_card
        rw [hidxM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'_le_T).toEquiv] at e1
        rw [hidxQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleM').toEquiv] at e2
        rw [← e1, ← e2]
      have hidxV := (hyp.V.subgroupOf hyp.T).index_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleT).toEquiv] at hidxV
      have hidxVeq : (hyp.V.subgroupOf hyp.T).index = Nat.card ↥hyp.Q * Nat.card ↥hyp.W2 := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥hyp.V))
        rw [hidxV, hTcard]; ring
      rw [hidxVeq]
      exact hcop.mul_right frobcop
    exact absurd (normalizer_le_of_isHall_subgroupOf_of_conj
        (_hG.isSolvable_of_mem_maximalSubgroups hyp.T_maximal) hVleT
        (isHall_subgroupOf_primeFactors_of_coprime_index hVleT hVhall_cop) hg hNVL) hNVT

end OddOrder.Peterfalvi.S15
