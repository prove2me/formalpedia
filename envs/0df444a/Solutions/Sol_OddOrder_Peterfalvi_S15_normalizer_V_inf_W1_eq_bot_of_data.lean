-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.normalizer_V_inf_W1_eq_bot_of_data
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:35.17822+00:00
-- url     : https://prove2.me/submissions/5c754f55-d9fc-45c0-a98b-ad9d11ee7407

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
import Theorems.Thm_OddOrder_Peterfalvi_S15_isMulCommutative_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_V_inf_W1_le_centralizer_W1

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

/-- **Peterfalvi (13.16), the `W₁`-side core assembly** (`V ⊓ N_G(W₁) = ⊥`, `T`-side dual of
`normalizer_U_inf_W2_eq_bot_of_data`).

Given the coprime-action datum `hcop : Coprime |Q| |V ⋊ W₂|`, the type-`P₂`-dual structure facts
`hQ_elemAb : Q` elementary abelian (14.2.a, `T`-side) and `hDbot : V ⊓ C_G(Q) = ⊥` (13.12 `d = 1`,
`T`-side), the assembly closes the `W₁`-side core from the proven crux `K ≤ C_G(W₁)`
(`normalizer_V_inf_W1_le_centralizer_W1`) exactly as on the `W₂`-side:

* the coprime `K`-action on the abelian `Q` decomposes `Q = (C_G(K) ⊓ Q) ⊕ ⁅Q, K⁆`
  (`fitting_coprime_abelian_decomp`, Gorenstein Thm 2.3);
* `W₂` acts fixed-point-freely on `⁅Q, K⁆`: a `W₂`-fixed `n ∈ ⁅Q, K⁆ ⊆ Q` lies in
  `T' ⊓ C_G(x) = tpd.W2 = W₁` (`TypePData.centralizer_W1` + the reconciliation `tpd.W2 = W₁`)
  `⊆ C_G(K) ⊓ Q`, so `n = 1`;
* the full `V ⋊ W₂` Frobenius (`typeP_uW1_frobenius`; `V` abelian ⟹ `V ≤ N_G(⁅Q,K⁆)`) centralizes
  `⁅Q, K⁆` by Wielandt (`frobenius_kernel_centralizes_of_complement_fpf`);
* so `⁅Q, K⁆ = ⊥`, i.e. `K ≤ C_G(Q)`, giving `K ≤ V ⊓ C_G(Q) = ⊥`.

The two structural inputs `hQ_elemAb`/`hDbot` are the `T`-side duals of `basic_structure`'s
`P_elementaryAbelian` and `U_inf_centralizer_P_eq_bot` (both (14.9)-`T_typeII`-gated); the rest is
proven group theory. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T)
    (hcop : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥(hyp.V ⊔ hyp.W2)))
    (hQ_elemAb : IsElementaryAbelian hyp.q ↥hyp.Q)
    (hDbot : hyp.V ⊓ Subgroup.centralizer (hyp.Q : Set G) = ⊥) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) = ⊥ := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
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
  have hVcomm : IsMulCommutative ↥hyp.V := isMulCommutative_V hG hyp ⟨tdata⟩
  set K := hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) with hK_def
  have hK_le_V : K ≤ hyp.V := inf_le_left
  -- crux: `K ≤ C_G(W₁)`.
  have hKC : K ≤ Subgroup.centralizer (hyp.W1 : Set G) :=
    normalizer_V_inf_W1_le_centralizer_W1 hG hyp ⟨tdata⟩
  -- `Q` abelian.
  have hQcomm : IsMulCommutative ↥hyp.Q := IsMulCommutative.of_comm hQ_elemAb.comm
  -- divisibilities `|K| ∣ |V| ∣ |V⋊W₂|`, from the coprime-action datum `hcop`.
  have hVdvdVW2 : Nat.card ↥hyp.V ∣ Nat.card ↥(hyp.V ⊔ hyp.W2) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hKdvdV : Nat.card ↥K ∣ Nat.card ↥hyp.V := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_V).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopQK : Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥K) :=
    hcop.coprime_dvd_right (hKdvdV.trans hVdvdVW2)
  -- normalizer facts: `T ≤ N(Q)`, `V ≤ T`, `W₂ ≤ T`, `W₂ ≤ N(W₁)`.
  have hMFleM : maxNilpotentNormalHall hyp.T ≤ hyp.T :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_norm_Q : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T)
  have hM'le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hV_le_T : hyp.V ≤ hyp.T :=
    le_trans (le_trans le_sup_right (le_of_eq hyp.T_deriv_eq_QV.symm)) hM'le
  have hW2_le_T : hyp.W2 ≤ hyp.T := htpdW1 ▸ tpd.W1_le
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    exact hyp.W1_commutes_W2 z hz x hx
  have hW2_le_N : hyp.W2 ≤ Subgroup.normalizer (hyp.W1 : Set G) :=
    hW2_le_C.trans (Subgroup.centralizer_le_normalizer _)
  have hK_norm_Q : K ≤ Subgroup.normalizer (hyp.Q : Set G) := (hK_le_V.trans hV_le_T).trans
      hT_norm_Q
  -- `V ≤ N(K)` (`V` abelian, `K ≤ V`).
  have hKnormalV : (K.subgroupOf hyp.V).Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  have hV_norm_K : hyp.V ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hK_le_V
  -- `W₂ ≤ N(K)` (`W₂ ≤ N(V)` and `W₂ ≤ N(N(W₁))`).
  have hW2_norm_K : hyp.W2 ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]; intro n
    have hwV := Subgroup.mem_normalizer_iff.mp (hyp.W2_normalizes_V hw) n
    have hwN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hW2_le_N hw)) n
    rw [hK_def, Subgroup.mem_inf, Subgroup.mem_inf, hwV, hwN]
  -- Gorenstein 2.3 decomposition `Q = (C(K) ⊓ Q) ⊕ ⁅Q, K⁆`.
  obtain ⟨hdec_inf, hdec_sup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp hK_norm_Q hcopQK
  have hQK_le_Q : (⁅hyp.Q, K⁆ : Subgroup G) ≤ hyp.Q := le_sup_right.trans (le_of_eq hdec_sup)
  -- `W₁ ≤ C(K) ⊓ Q`.
  have hW1_le_Q' : hyp.W1 ≤ hyp.Q := W1_le_Q hG hyp
  have hW1_le_CK : hyp.W1 ≤ Subgroup.centralizer (K : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    exact ((Subgroup.mem_centralizer_iff.mp (hKC hk)) y hy).symm
  -- Wielandt: `V ≤ C(⁅Q,K⁆)`.
  have hVEnorm : hyp.V ⊔ hyp.W2 ≤ Subgroup.normalizer ((⁅hyp.Q, K⁆ : Subgroup G) : Set G) := by
    rw [sup_le_iff]
    refine ⟨fun v hv => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator ((hV_le_T.trans hT_norm_Q)
        hv)
      (hV_norm_K hv), fun w hw => OddOrder.BG.Ch1.S03f.mem_normalizer_commutator
      ((hW2_le_T.trans hT_norm_Q) hw) (hW2_norm_K hw)⟩
  have hQKsolv : Group.IsSolvable ↥(⁅hyp.Q, K⁆ : Subgroup G) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (by
      have h := hQ_elemAb.comm (⟨(a : G), hQK_le_Q a.2⟩ : ↥hyp.Q) (⟨(b : G), hQK_le_Q b.2⟩ : ↥hyp.Q)
      have h2 := congrArg (Subgroup.subtype hyp.Q) h
      simpa using h2))
  have hQKdvdQ : Nat.card ↥(⁅hyp.Q, K⁆ : Subgroup G) ∣ Nat.card ↥hyp.Q := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK_le_Q).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcopQKfrob : Nat.Coprime (Nat.card ↥(⁅hyp.Q, K⁆ : Subgroup G))
      (Nat.card ↥(hyp.V ⊔ hyp.W2)) := hcop.coprime_dvd_left hQKdvdQ
  have hVcent : hyp.V ≤ Subgroup.centralizer ((⁅hyp.Q, K⁆ : Subgroup G) : Set G) :=
    frobenius_kernel_centralizes_of_complement_fpf hVEnorm hVW2frob hQKsolv hcopQKfrob
      (by
        intro n hnQK hnfix
        -- `n ∈ ⁅Q,K⁆ ⊆ Q` fixed by all of `W₂` ⟹ `n ∈ tpd.W2 = W₁ ⊆ C(K) ⊓ Q` ⟹ `n = 1`.
        have hnQ : n ∈ hyp.Q := hQK_le_Q hnQK
        have hW2ne : tpd.W1 ≠ ⊥ := tpd.W1_nontrivial
        have : Nontrivial ↥tpd.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW2ne
        obtain ⟨x0, hx0⟩ := exists_ne (1 : ↥tpd.W1)
        have hxW2 : (x0 : G) ∈ hyp.W2 := htpdW1 ▸ x0.2
        have hxne : (x0 : G) ≠ 1 := fun h => hx0 (OneMemClass.coe_eq_one.mp h)
        have hnCx : (x0 : G) * n * (x0 : G)⁻¹ = n := hnfix _ hxW2
        have hnCent : n ∈ Subgroup.centralizer ({(x0 : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]; intro z hz
          rw [Set.mem_singleton_iff] at hz; subst hz
          exact (mul_inv_eq_iff_eq_mul.mp hnCx)
        have hnM' : n ∈ derivedInG hyp.T := by
          have hQM' : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
          exact hQM' hnQ
        have hreg := tpd.centralizer_W1 (x0 : G) x0.2 hxne
        have hnW1 : n ∈ hyp.W1 := by
          rw [← htpdW2, ← hreg]; exact Subgroup.mem_inf.mpr ⟨hnM', hnCent⟩
        have hnInf : n ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.Q) ⊓ (⁅hyp.Q, K⁆ : Subgroup G) :=
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hW1_le_CK hnW1, hnQ⟩, hnQK⟩
        rw [hdec_inf, Subgroup.mem_bot] at hnInf
        exact hnInf)
  -- `⁅Q,K⁆ ≤ C(K) ⊓ Q`, hence `⁅Q,K⁆ = ⊥`.
  have hQK_le_CK : (⁅hyp.Q, K⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]; intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hVcent (hK_le_V hk)) x hx).symm
  have hQK_bot : (⁅hyp.Q, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (Subgroup.centralizer (K : Set G) ⊓ hyp.Q) ⊓ (⁅hyp.Q, K⁆ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hQK_le_CK hx, hQK_le_Q hx⟩, hx⟩
    rwa [hdec_inf] at this
  -- `⁅Q,K⁆ = ⊥ ⟹ K ≤ C(Q) ⟹ K ≤ V ⊓ C(Q) = ⊥`.
  have hK_le_CQ : K ≤ Subgroup.centralizer (hyp.Q : Set G) := by
    have hQcentK : hyp.Q ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := hyp.Q) (H₂ := K)).mp hQK_bot
    intro k hk
    rw [Subgroup.mem_centralizer_iff]; intro q hq
    exact ((Subgroup.mem_centralizer_iff.mp (hQcentK hq)) k hk).symm
  have : K ≤ hyp.V ⊓ Subgroup.centralizer (hyp.Q : Set G) := le_inf hK_le_V hK_le_CQ
  rw [hDbot] at this
  exact le_bot_iff.mp this

end OddOrder.Peterfalvi.S15
