-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.isMulCommutative_V
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:32.663107+00:00
-- url     : https://prove2.me/submissions/6ef90bbf-59c9-4f30-a352-5681f83995d3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_V_card_Q_of_disjoint

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`T`-side analogue of the carried `S_U_commutative` fact** (Pf (13.2.a), V-side): the
complement
`V` of the type-II member `T` is commutative.  Here `IsTypeII T` is a hypothesis
(the (14.9) `T_typeII` conclusion, supplied by the caller).  Sources the `T`-side type-`P` structure
from the off-spine `reconciled_typePData_T` (not the withdrawn `Tdata` carrier). -/
theorem _root_.solution [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) : IsMulCommutative ↥hyp.V := by
  obtain ⟨tdata⟩ := hTTypeII
  -- `Q ⊓ V = ⊥` is now the honest `Hypothesis` field `Q_inf_V_eq_bot` (threaded from the §16
  -- constructor's `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)), replacing the
  -- former circular route through the then-sorried `reconciled_typePData_T`.
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
  have hQH : hyp.Q = tdata.typeP.H := by rw [hyp.Q_eq_TF, tdata.typeP.H_eq]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hdisj, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hV'compl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.T)) := by
    rw [hQH]; exact tdata.typeP.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv, hVcompl.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]
    exact (coprime_card_V_card_Q_of_disjoint hyp tdata hdisj).symm
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  have hQsolv : Group.IsSolvable ↥hyp.Q := _hG.isSolvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : Group.IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      Group.IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hVcompl hV'compl
  have h2 : IsMulCommutative ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe tdata.typeP.U_le).symm tdata.U_commutative
  rw [← hn] at h2
  have h4 : IsMulCommutative ↥(hyp.V.subgroupOf (derivedInG hyp.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective).symm h2
  exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hV_le) h4

end OddOrder.Peterfalvi.S15
