-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.mSide_dadeSupport_avoids_regular
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:32:06.85432+00:00
-- url     : https://prove2.me/submissions/dbf5ed1f-5d4e-47c0-90f3-238240926aaa

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality

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

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b)/(14.2.a), `T`-side dual of `W2_le_P`: `W₁ ≤ Q`.**  The cyclic factor `W₁`
(of prime order `q`) lies in `Q = T_F`, the maximal nilpotent normal Hall subgroup of `T`.  Dual to
`W2_le_P` (`W₂ ≤ P`), but read off the `T`-side type-`P` decomposition (`reconciled_typePData_T`)
rather than the coprime-index order count: the intrinsic dual cyclic factor
`data.W2 = C_{T'}(W₂#) = W₁` sits inside `data.H = maxNilpotentNormalHall T = Q`
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16)
`normalizer_W1_structure_of_D_eq_bot`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

end OddOrder.Peterfalvi.S15

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
/-- **Peterfalvi (13.19.a), σ-decomposition ingredient**: the Fitting core `M_F`
(`dataM.kernel`) of the type-`I` maximal `M`, non-conjugate to the `W`-containing maximals
`S`, `T`, has order coprime to `p·q`.  In the Coq proof of `tiA_PWG` this is `coHp`/`coHq`
(`coprime #|H| p`, `coprime #|H| q` with `H = M_F`), derived from `FT_Dade_support_partition`:
`p, q ∈ σ(S) ∪ σ(T)` are disjoint from `σ(M)` for non-conjugate maximals (`nc.not_conj`).
Deep named §13/BG §10 obligation. -/
theorem card_kernel_coprime_pq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (_hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (_hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    Nat.Coprime (Nat.card ↥dataM.kernel) (hyp.base.p * hyp.base.q) := by
  classical
  -- `M`, `S`, `T` are maximal; `M` is type I and `S`/`T` are type non-I.
  have hMI : IsTypeI M := ⟨dataM.typeIHyp.typeI⟩
  -- `M_F = M_σ`; for `S` and `T` the general inclusions `F(-) ≤ (-)_σ` suffice.
  have hMF : dataM.kernel = OddOrder.BG.Ch3.S10.Msigma M := by
    change dataM.typeIHyp.typeI.typeF.H = _
    rw [dataM.typeIHyp.typeI.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hMmax (Or.inl hMI)
  have hPleS : hyp.base.P ≤ OddOrder.BG.Ch3.S10.Msigma hyp.base.S := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.base.S_maximal
  have hQleT : hyp.base.Q ≤ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.base.T_maximal
  -- `p ∈ σ(S)` via `W₂ ≤ P ≤ S_σ`; similarly `q ∈ σ(T)` via `W₁ ≤ Q ≤ T_σ`.
  have hpσS : hyp.base.p ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.S := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.S_maximal]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.p_eq_card_W2]
    exact Subgroup.card_dvd_of_le
      ((OddOrder.Peterfalvi.S15.W2_le_P hG hyp.base).trans hPleS)
  have hqσT : hyp.base.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.base.T := by
    rw [← OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hyp.base.T_maximal]
    refine Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, ?_, Nat.card_pos.ne'⟩
    rw [hyp.base.q_eq_card_W1]
    exact Subgroup.card_dvd_of_le
      ((OddOrder.Peterfalvi.S15.W1_le_Q hG hyp.base).trans hQleT)
  -- `M` is not conjugate to `S` or `T` (type I vs type non-I) ⟹ `σ`-disjointness
  have hMnS : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.S :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.S_maximal
      hyp.base.S_nonI
  have hMnT : ¬ ∃ g : G, MulAut.conj g • M = hyp.base.T :=
    OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI hG hMI hyp.base.T_maximal
      hyp.base.T_nonI
  have hdS := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.S_maximal hMnS
  have hdT := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hyp.base.T_maximal hMnT
  -- hence `p, q ∉ σ(M) = π(|M_F|)`, so `p, q ∤ |M_F|`
  have hpMF : ¬ hyp.base.p ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdS
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.p).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.p_prime, hdvd, Nat.card_pos.ne'⟩)) hpσS
  have hqMF : ¬ hyp.base.q ∣ Nat.card ↥dataM.kernel := by
    rw [hMF]; intro hdvd
    exact Set.disjoint_left.mp hdT
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hMmax hyp.base.q).mp
        (Nat.mem_primeFactors.mpr ⟨hyp.base.q_prime, hdvd, Nat.card_pos.ne'⟩)) hqσT
  exact Nat.Coprime.mul_right
    (hyp.base.p_prime.coprime_iff_not_dvd.mpr hpMF).symm
    (hyp.base.q_prime.coprime_iff_not_dvd.mpr hqMF).symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), Dade-support ingredient**: every element `y` of the Dade support
`Ã(M) = ⋃_{x∈A(M)} (x·R(x))^G` has order *not* coprime to `|M_F|` (it is `π(M_F)`-singular).
Indeed `y` is conjugate to `x·r` with `x ∈ A(M) = M_F^#` (type-I, `1 ≠ x ∈ M_F`) and
`r ∈ R(x)` a signalizer commuting with `x` of order coprime to `|M_F|`, so
`1 < orderOf x ∣ orderOf y` and `orderOf x ∣ |M_F|`.  Deep named §8/§13 obligation
(the Dade signalizer `π`-part structure). -/
theorem dadeSupport_not_coprime_card_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (dataM : TypeICoherent78Data M)
    {y : G} (hy : y ∈ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport) :
    ¬ Nat.Coprime (orderOf y) (Nat.card ↥dataM.kernel) := by
  classical
  -- `y` is conjugate to `a·h` with `a ∈ A = M_F#`, `h ∈ H(a)` (the (8.14) signalizer)
  rw [dataM.h78_hyp_eq hG, OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff] at hy
  obtain ⟨a, h, hh, hconj⟩ := hy
  -- `a.1 ∈ M_F`, `a.1 ≠ 1` (`A = typeIA = M_F ∖ {1}`)
  have ha2 : a.1 ∈ (dataM.kernel : Set G) \ {1} := by
    rw [← dataM.typeIA_eq_sharp]; exact a.2
  have haK : a.1 ∈ dataM.kernel := ha2.1
  have hane : a.1 ≠ 1 := fun h1 => ha2.2 (Set.mem_singleton_iff.mpr h1)
  have hord_ne : orderOf a.1 ≠ 1 := fun h1 => hane (orderOf_eq_one_iff.mp h1)
  have hord_dvd : orderOf a.1 ∣ Nat.card ↥dataM.kernel := dataM.kernel.orderOf_dvd_natCard haK
  -- `h` commutes with `a.1`: `H(a) ≤ C_G(a.1)` by `(2.2.b)` `C_G(a.1) = H(a) ⊔ C_L(a.1)`
  have hh_cent : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
    rw [(dataM.typeIHyp.dadeData.dade).centralizer_eq_sup a]
    exact Subgroup.mem_sup_left hh
  have hcomm : Commute a.1 h := (Subgroup.mem_centralizer_singleton_iff.mp hh_cent).symm
  -- `orderOf a.1` coprime `orderOf h`: `(2.2.c)` `(|H(a)|, |C_L(a.1)|) = 1`
  have hcop_orders : Nat.Coprime (orderOf a.1) (orderOf h) := by
    have hcc := (dataM.typeIHyp.dadeData.dade).centralizer_coprime a a
    have hord_h : orderOf h ∣ Nat.card ↥((dataM.typeIHyp.dadeData.dade).H a) :=
      ((dataM.typeIHyp.dadeData.dade).H a).orderOf_dvd_natCard hh
    have haCent : a.1 ∈ OddOrder.Peterfalvi.S04.centralizerIn M a.1 :=
      OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
        ⟨(dataM.typeIHyp.dadeData.dade).mem_L a.2, rfl⟩
    have hord_a : orderOf a.1 ∣ Nat.card ↥(OddOrder.Peterfalvi.S04.centralizerIn M a.1) :=
      (OddOrder.Peterfalvi.S04.centralizerIn M a.1).orderOf_dvd_natCard haCent
    exact (Nat.Coprime.coprime_dvd_right hord_a
      (Nat.Coprime.coprime_dvd_left hord_h hcc)).symm
  -- `orderOf y = orderOf(a.1·h) = orderOf a.1 · orderOf h`, so `orderOf a.1 ∣ orderOf y`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hsemi : SemiconjBy c (a.1 * h) y := by
    change c * (a.1 * h) = y * c; rw [← hc]; group
  have hordy : orderOf y = orderOf a.1 * orderOf h := by
    rw [← SemiconjBy.orderOf_eq c hsemi,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop_orders]
  have hdvd_y : orderOf a.1 ∣ orderOf y := by rw [hordy]; exact dvd_mul_right _ _
  -- `1 < orderOf a.1 ∣ gcd(orderOf y, |M_F|) = 1` is a contradiction
  intro hcop
  have hcop' : Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) = 1 := hcop
  have hgcd : orderOf a.1 ∣ Nat.gcd (orderOf y) (Nat.card ↥dataM.kernel) :=
    Nat.dvd_gcd hdvd_y hord_dvd
  rw [hcop'] at hgcd
  exact hord_ne (Nat.dvd_one.mp hgcd)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.a), the M-side Dade-support avoidance.**  For a type-`I` maximal
`M` not conjugate to the `W`-containing maximals `S`, `T`, the Dade support `Ã(M)` avoids the
regular-set saturation `Ŵ^G = (W ∖ (W₁ ∪ W₂))^G`.  This is the Coq `tiA_PWG`
(`'A~(L) :&: PWG = set0`, PFsection13): every `x ∈ Ŵ^G` is conjugate to a `w ∈ W`, so (as
`|W₁| = q`, `|W₂| = p` are prime and `W = W₁·W₂` commutes) `orderOf x ∣ p·q`, hence `orderOf x`
is coprime to `|M_F|` (`card_kernel_coprime_pq`); but every element of `Ã(M)` is
`π(M_F)`-singular (`dadeSupport_not_coprime_card_kernel`), a contradiction.  The two named
ingredients are the genuine BG §10-level σ-decomposition inputs. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    {hyp : Hypothesis (G := G)}
    {M : Subgroup G} (hMmax : M ∈ maximalSubgroups G) (dataM : TypeICoherent78Data M) :
    ∀ x ∈ conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))),
      x ∉ (dataM.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
  intro x hx hdade
  obtain ⟨w, ⟨hwW, _hwne⟩, g, hgx⟩ := hx
  -- `orderOf x = orderOf w` (conjugation preserves order)
  have hsemi : SemiconjBy g w x := by
    change g * w = x * g
    rw [← hgx]; group
  have hordx : orderOf x = orderOf w := (SemiconjBy.orderOf_eq g hsemi).symm
  -- decompose `w = a·b` with `a ∈ W₁`, `b ∈ W₂` inside the commutative `W`
  let := hyp.base.W_cyclic
  let : CommGroup ↥hyp.base.W := IsCyclic.commGroup
  have hwWmem : w ∈ hyp.base.W := hwW
  have hW1le : hyp.base.W1 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
  have hwmem : (⟨w, hwWmem⟩ : ↥hyp.base.W) ∈
      (hyp.base.W1.subgroupOf hyp.base.W) ⊔ (hyp.base.W2.subgroupOf hyp.base.W) := by
    have h1 : (hyp.base.W1 ⊔ hyp.base.W2).subgroupOf hyp.base.W = ⊤ := by
      rw [← hyp.base.W_eq_join, Subgroup.subgroupOf_self]
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, h1]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hwmem
  have hcoe : (a : G) * (b : G) = w := by
    have h := congrArg (Subtype.val) hab; simpa using h
  have haW1 : (a : G) ∈ hyp.base.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : (b : G) ∈ hyp.base.W2 := Subgroup.mem_subgroupOf.mp hb
  -- `orderOf a ∣ q`, `orderOf b ∣ p` (Lagrange in the prime-order `W₁`, `W₂`)
  have haord : orderOf (a : G) ∣ hyp.base.q := by
    have h := hyp.base.W1.orderOf_dvd_natCard haW1
    rwa [← hyp.base.q_eq_card_W1] at h
  have hbord : orderOf (b : G) ∣ hyp.base.p := by
    have h := hyp.base.W2.orderOf_dvd_natCard hbW2
    rwa [← hyp.base.p_eq_card_W2] at h
  have hcomm : Commute (a : G) (b : G) := hyp.base.W1_commutes_W2 _ haW1 _ hbW2
  -- hence `orderOf x = orderOf w ∣ p·q`
  have hword : orderOf w ∣ hyp.base.p * hyp.base.q := by
    rw [← hcoe]
    refine hcomm.orderOf_mul_dvd_mul_orderOf.trans ?_
    rw [mul_comm hyp.base.p hyp.base.q]
    exact Nat.mul_dvd_mul haord hbord
  have hxord : orderOf x ∣ hyp.base.p * hyp.base.q := hordx ▸ hword
  -- `orderOf x` is coprime to `|M_F|`, contradicting `π(M_F)`-singularity of `Ã(M)`
  have hcop : Nat.Coprime (orderOf x) (Nat.card ↥dataM.kernel) :=
    Nat.Coprime.coprime_dvd_left hxord (card_kernel_coprime_pq hG hnoV hncH0C hMmax dataM).symm
  exact dadeSupport_not_coprime_card_kernel hG dataM hdade hcop

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
