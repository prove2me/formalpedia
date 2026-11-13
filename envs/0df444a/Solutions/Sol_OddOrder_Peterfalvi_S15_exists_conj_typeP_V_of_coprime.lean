-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.exists_conj_typeP_V_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:40.899415+00:00
-- url     : https://prove2.me/submissions/e818436e-69a9-4db3-89ee-442cf61fb29d

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
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`T`-side dual of `exists_conj_typeP_U_of_coprime`** (Pf (13.17), V-side): for the type-II
member `T`, if `|V|` is coprime to `|Q| = |T_F|`, then `V` is a `T`-conjugate of the `TypeIIData`
witness's complement `tdata.typeP.U` (both complement `Q` in `T' = [T,T]`, Schur–Zassenhaus). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (tdata : TypeIIData hyp.T)
    (hcop : Nat.Coprime (Nat.card ↥hyp.V) (Nat.card ↥hyp.Q)) :
    ∃ x : G, x ∈ hyp.T ∧ hyp.V = MulAut.conj x • tdata.typeP.U := by
  have hQH : hyp.Q = tdata.typeP.H := by rw [hyp.Q_eq_TF, tdata.typeP.H_eq]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have htU_le : tdata.typeP.U ≤ derivedInG hyp.T := tdata.typeP.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hTsolv : Group.IsSolvable ↥hyp.T := hG.isSolvable_of_mem_maximalSubgroups hyp.T_maximal
  have hM'solv : Group.IsSolvable ↥(derivedInG hyp.T) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM'_le_T)
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hM'_le_NQ : derivedInG hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) :=
    hM'_le_T.trans hT_le_NQ
  have hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr hM'_le_NQ
  have hKcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.T)) := by
    rw [hQH]; exact tdata.typeP.derived_complement
  have hcop' : Nat.Coprime (Nat.card ↥(hyp.V.subgroupOf (derivedInG hyp.T)))
      (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv]
    exact hcop
  have hQV_eq : hyp.Q ⊔ hyp.V = derivedInG hyp.T := hyp.T_deriv_eq_QV.symm
  have hQnVn_sup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
      (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hQV_eq, Subgroup.subgroupOf_self]
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · exact Subgroup.disjoint_of_coprime_natCard hcop'.symm
    · have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hQnVn_sup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hcardV : Nat.card ↥hyp.V = Nat.card ↥tdata.typeP.U := by
    have hVcong : Nat.card ↥(hyp.V.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv
    have hKcong : Nat.card ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.T)) =
        Nat.card ↥tdata.typeP.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe htU_le).toEquiv
    have hQpos : 0 < Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) := Nat.card_pos
    have key := Nat.eq_of_mul_eq_mul_left hQpos
      (hVcompl.card_mul_card.trans hKcompl.card_mul_card.symm)
    rw [← hVcong, ← hKcong]; exact key
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    (M := hyp.Q.subgroupOf (derivedInG hyp.T))
    (K := tdata.typeP.U.subgroupOf (derivedInG hyp.T))
    (U := hyp.V.subgroupOf (derivedInG hyp.T))
    inferInstance hKcompl hcop'
  have hsmul_map : ∀ K : Subgroup G,
      MulAut.conj (x : G) • K = K.map (MulAut.conj (x : G)).toMonoidHom := by
    intro K; rw [Subgroup.pointwise_smul_def]; rfl
  have hintertwine : (derivedInG hyp.T).subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp (derivedInG hyp.T).subtype := by
    ext ⟨y, hy⟩; rfl
  have hRHS : (((tdata.typeP.U.subgroupOf (derivedInG hyp.T)).map
        (MulAut.conj x).toMonoidHom).map (derivedInG hyp.T).subtype)
      = MulAut.conj (x : G) • tdata.typeP.U := by
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le htU_le, hsmul_map]
  have hle : hyp.V ≤ MulAut.conj (x : G) • tdata.typeP.U := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hV_le, ← hRHS]
    exact Subgroup.map_mono hx
  have hconj_card : Nat.card ↥(MulAut.conj (x : G) • tdata.typeP.U) =
      Nat.card ↥tdata.typeP.U := by
    rw [hsmul_map]; exact Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective
  refine ⟨(x : G), hM'_le_T x.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [hconj_card, hcardV]

end OddOrder.Peterfalvi.S15
