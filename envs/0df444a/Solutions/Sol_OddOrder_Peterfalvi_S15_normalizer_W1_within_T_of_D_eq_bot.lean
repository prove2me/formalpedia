-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.normalizer_W1_within_T_of_D_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:36.401446+00:00
-- url     : https://prove2.me/submissions/20159b03-8b6d-44cc-a53a-50fbb71aa661

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
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T
import Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_V_inf_W1_eq_bot_of_data
import Theorems.Thm_OddOrder_Peterfalvi_S15_coprime_card_Q_card_VW2

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

/-- **Peterfalvi (13.16), explicit-`D = ⊥` Maschke/Wielandt core for the `W₁`-side**:
`N_G(W₁) ⊓ T ≤ Q ⊔ W₂`.

The `T`-side dual of `normalizer_W2_within_S`.  The `T`-internal residual of the (13.16)
`W₁`-confinement (after the TI reduction `N_G(W₁) ≤ T` of `normalizer_W1_le_T`).  Reduced by the
**Dedekind modular law** to the core `N_V(W₁) = ⊥`
(`normalizer_V_inf_W1_eq_bot_of_data`): writing
`T = (Q ⊔ V) ⊔ W₂` (`T_deriv_eq_QV` + the reconciled complement `M' ⋊ W₂ = T`), and using
`Q, W₂ ≤ C_G(W₁) ≤ N_G(W₁)` (`Q` elementary abelian, `W = W₁ × W₂` abelian), modularity peels off
`W₂` and `Q`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) (hDbot : hyp.D = ⊥) :
    Subgroup.normalizer (hyp.W1 : Set G) ⊓ hyp.T ≤ hyp.Q ⊔ hyp.W2 := by
  obtain ⟨tpd, _, htpdW1, _⟩ := reconciled_typePData_T hG hyp
  have hK : hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ :=
    normalizer_V_inf_W1_eq_bot_of_data hG hyp hTTypeII (coprime_card_Q_card_VW2 hG hyp)
      (Q_elementaryAbelian_T hG hyp hTTypeII) (by rw [← hyp.D_eq]; exact hDbot)
  -- `W₂ ≤ C_G(W₁)`: `W = W₁ × W₂` is abelian.
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hyp.W1_commutes_W2 y (SetLike.mem_coe.mp hy) x hx
  -- `Q ≤ C_G(W₁)`: `W₁ ≤ Q` and `Q` elementary abelian give `Q` centralizes `W₁`.
  have hQ_le_C : hyp.Q ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    have hQ_elemAb := Q_elementaryAbelian_T hG hyp hTTypeII
    have hW1Q := W1_le_Q hG hyp
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : y ∈ hyp.Q := hW1Q (SetLike.mem_coe.mp hy)
    have h := hQ_elemAb.comm (⟨y, hyQ⟩ : ↥hyp.Q) (⟨g, hg⟩ : ↥hyp.Q)
    have h2 := congrArg (Subgroup.subtype hyp.Q) h
    simpa using h2
  have hQ_le_N : hyp.Q ≤ Subgroup.normalizer (hyp.W1 : Set G) :=
    hQ_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hW2_le_N : hyp.W2 ≤ Subgroup.normalizer (hyp.W1 : Set G) :=
    hW2_le_C.trans (Subgroup.centralizer_le_normalizer _)
  -- `Q ⊴ T` and `M' := derivedInG T ⊴ T`, so `T ≤ N_G(Q)` and `T ≤ N_G(M')`.
  have hMFleM : maxNilpotentNormalHall hyp.T ≤ hyp.T :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_norm_Q : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T)
  have hM'le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hM'_normal : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by
    rw [show (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective]]
    infer_instance
  have hT_norm_M' : hyp.T ≤ Subgroup.normalizer ((derivedInG hyp.T : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM'le).mp hM'_normal
  have hV_le_T : hyp.V ≤ hyp.T :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.T_deriv_eq_QV.symm)) hM'le
  have hW2_le_T : hyp.W2 ≤ hyp.T := htpdW1 ▸ tpd.W1_le
  -- `T = derivedInG T ⊔ W₂` (the reconciled complement `M' ⋊ W₂ = T`).
  have hTsup : derivedInG hyp.T ⊔ hyp.W2 = hyp.T := by
    have htop := tpd.M_complement.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.T.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'le,
      Subgroup.map_subgroupOf_eq_of_le tpd.W1_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [htpdW1] at hmap
    exact hmap
  -- **Sub-goal A** (Dedekind): `M' ⊓ N_G(W₁) = Q`.
  have hHV : ((derivedInG hyp.T) ⊓ Subgroup.normalizer (hyp.W1 : Set G)) ⊓ hyp.V = ⊥ := by
    refine le_bot_iff.mp (le_trans (inf_le_inf_right hyp.V inf_le_right) ?_)
    rw [inf_comm]; exact hK.le
  have hQ_le_M' : hyp.Q ≤ derivedInG hyp.T :=
    le_trans le_sup_left (le_of_eq hyp.T_deriv_eq_QV.symm)
  have hMN : (derivedInG hyp.T) ⊓ Subgroup.normalizer (hyp.W1 : Set G) = hyp.Q := by
    have happ := OddOrder.BG.Ch3.S12.eq_sup_inf_of_le_normalizer (hV_le_T.trans hT_norm_Q)
      (le_inf hQ_le_M' hQ_le_N) (inf_le_left.trans (le_of_eq hyp.T_deriv_eq_QV))
    rw [happ, hHV, sup_bot_eq]
  -- **Sub-goal B** (element-wise): `g ∈ N_G(W₁) ⊓ T`; write `g = w·m` (`w ∈ W₂`, `m ∈ M'`).
  intro g hg
  obtain ⟨hgN, hgT⟩ := Subgroup.mem_inf.mp hg
  have hmem : (g : G) ∈ ((hyp.W2 : Set G) * (derivedInG hyp.T : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right hyp.W2 (derivedInG hyp.T)
      (hW2_le_T.trans hT_norm_M'), SetLike.mem_coe, sup_comm, hTsup]
    exact hgT
  obtain ⟨w, hw, m, hm, hwm⟩ := Set.mem_mul.mp hmem
  have hmN : m ∈ Subgroup.normalizer (hyp.W1 : Set G) := by
    have hm_eq : m = w⁻¹ * g := by rw [← hwm]; group
    rw [hm_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hW2_le_N (SetLike.mem_coe.mp hw))) hgN
  have hmQ : m ∈ hyp.Q := by
    have hmem2 : m ∈ (derivedInG hyp.T) ⊓ Subgroup.normalizer (hyp.W1 : Set G) :=
      Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hm, hmN⟩
    rwa [hMN] at hmem2
  rw [← hwm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (SetLike.mem_coe.mp hw))
    (Subgroup.mem_sup_left hmQ)

end OddOrder.Peterfalvi.S15
