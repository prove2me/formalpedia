-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.exists_conj_typeP_U_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:02.642834+00:00
-- url     : https://prove2.me/submissions/842085b6-00da-430e-bdde-81f09525a3e6

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_SAndTDefs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Schur–Zassenhaus conjugacy for the (13.17) coherence bridge**: when the configuration
complement `U` is coprime to `P = S_F`, it is conjugate (by an element of `S`) to the type-data
complement `typeP.U`.

Both `U` and `typeP.U` complement the normal Hall subgroup `P` in `M' = derivedInG S`: `P ◁ M'`
(since `M' ≤ S ≤ N_G(P)`) is solvable, `M' = P ⊔ typeP.U` is the `derived_complement` field, and
`M' = P ⊔ U` is `S_deriv_eq_PU`.  Coprimality `Nat.Coprime |U| |P|` forces `P ⊓ U = ⊥`, so `U` is a
genuine `P`-complement of the same order as `typeP.U`; Schur–Zassenhaus
(`exists_conj_le_of_isComplement'_of_coprime`, applied inside `↥M'`) then conjugates `typeP.U` onto
`U`.  This discharges the `hconj` hypothesis of `not_normalizer_U_le_S`; the coprimality is the
(13.2) faithfulness datum supplied by the enriched §16 Hypothesis (Phase 0(b)). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (tdata : TypeIIData hyp.S)
    (hcop : Nat.Coprime (Nat.card ↥hyp.U) (Nat.card ↥hyp.P)) :
    ∃ x : G, x ∈ hyp.S ∧ hyp.U = MulAut.conj x • tdata.typeP.U := by
  -- `P = typeP.H` and the containments in `M' = derivedInG S`.
  have hPH : hyp.P = tdata.typeP.H := by rw [hyp.P_eq_SF, tdata.typeP.H_eq]
  have hP_le : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hU_le : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have htU_le : tdata.typeP.U ≤ derivedInG hyp.S := tdata.typeP.U_le
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  -- Solvability of `↥M'` (fix ii: transport along the injective inclusion `↥M' ↪ ↥S`).
  have hSsolv : Group.IsSolvable ↥hyp.S := hG.isSolvable_of_mem_maximalSubgroups hyp.S_maximal
  have hM'solv : Group.IsSolvable ↥(derivedInG hyp.S) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM'_le_S)
  -- `P ◁ M'` (fix iv: `normal_subgroupOf_iff_le_normalizer`, set-form normalizer).
  have hS_le_NP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hM'_le_NP : derivedInG hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) :=
    hM'_le_S.trans hS_le_NP
  have hPn_normal : (hyp.P.subgroupOf (derivedInG hyp.S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le).mpr hM'_le_NP
  -- `typeP.U` complements `P` in `M'` (the `derived_complement` field, rewritten via
  -- `P = typeP.H`).
  have hKcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (tdata.typeP.U.subgroupOf (derivedInG hyp.S)) := by
    rw [hPH]; exact tdata.typeP.derived_complement
  -- Coprimality transported into `↥M'`.
  have hcop' : Nat.Coprime (Nat.card ↥(hyp.U.subgroupOf (derivedInG hyp.S)))
      (Nat.card ↥(hyp.P.subgroupOf (derivedInG hyp.S))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le).toEquiv]
    exact hcop
  -- `U` also complements `P` in `M'` (join from `S_deriv_eq_PU`, disjoint from coprimality).
  have hPU_eq : hyp.P ⊔ hyp.U = derivedInG hyp.S := hyp.S_deriv_eq_PU.symm
  have hPnUn_sup : (hyp.P.subgroupOf (derivedInG hyp.S)) ⊔
      (hyp.U.subgroupOf (derivedInG hyp.S)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP_le hU_le, hPU_eq, Subgroup.subgroupOf_self]
  have hUcompl : (hyp.P.subgroupOf (derivedInG hyp.S)).IsComplement'
      (hyp.U.subgroupOf (derivedInG hyp.S)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · exact Subgroup.disjoint_of_coprime_natCard hcop'.symm
    · have hmul := Subgroup.normal_mul (hyp.P.subgroupOf (derivedInG hyp.S))
        (hyp.U.subgroupOf (derivedInG hyp.S))
      rw [hPnUn_sup, Subgroup.coe_top] at hmul
      exact hmul.symm
  -- `|U| = |typeP.U|` (both complement `P` in `M'`, so both have index `[M' : P]`).
  have hcardU : Nat.card ↥hyp.U = Nat.card ↥tdata.typeP.U := by
    have hUcong : Nat.card ↥(hyp.U.subgroupOf (derivedInG hyp.S)) = Nat.card ↥hyp.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le).toEquiv
    have hKcong : Nat.card ↥(tdata.typeP.U.subgroupOf (derivedInG hyp.S)) =
        Nat.card ↥tdata.typeP.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe htU_le).toEquiv
    have hPpos : 0 < Nat.card ↥(hyp.P.subgroupOf (derivedInG hyp.S)) := Nat.card_pos
    have key := Nat.eq_of_mul_eq_mul_left hPpos
      (hUcompl.card_mul_card.trans hKcompl.card_mul_card.symm)
    rw [← hUcong, ← hKcong]; exact key
  -- Schur–Zassenhaus inside `↥M'`: `U.subgroupOf M' ≤ (typeP.U.subgroupOf M')ᶜᵒⁿʲ` by some
  -- `x ∈ M'`.
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime
    (M := hyp.P.subgroupOf (derivedInG hyp.S))
    (K := tdata.typeP.U.subgroupOf (derivedInG hyp.S))
    (U := hyp.U.subgroupOf (derivedInG hyp.S))
    inferInstance hKcompl hcop'
  -- Map the conjugacy back to `G` (fix v: intertwine `M'.subtype` with `conj`).
  have hsmul_map : ∀ K : Subgroup G,
      MulAut.conj (x : G) • K = K.map (MulAut.conj (x : G)).toMonoidHom := by
    intro K; rw [Subgroup.pointwise_smul_def]; rfl
  have hintertwine : (derivedInG hyp.S).subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp (derivedInG hyp.S).subtype := by
    ext ⟨y, hy⟩; rfl
  have hRHS : (((tdata.typeP.U.subgroupOf (derivedInG hyp.S)).map
        (MulAut.conj x).toMonoidHom).map (derivedInG hyp.S).subtype)
      = MulAut.conj (x : G) • tdata.typeP.U := by
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le htU_le, hsmul_map]
  have hle : hyp.U ≤ MulAut.conj (x : G) • tdata.typeP.U := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hU_le, ← hRHS]
    exact Subgroup.map_mono hx
  have hconj_card : Nat.card ↥(MulAut.conj (x : G) • tdata.typeP.U) =
      Nat.card ↥tdata.typeP.U := by
    rw [hsmul_map]; exact Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective
  -- Upgrade containment to equality via the matching orders.
  refine ⟨(x : G), hM'_le_S x.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [hconj_card, hcardU]

end OddOrder.Peterfalvi.S15
