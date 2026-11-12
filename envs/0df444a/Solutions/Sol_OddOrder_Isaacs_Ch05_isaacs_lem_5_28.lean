-- Prove2me | solution 1 for OddOrder.Isaacs.Ch05.isaacs_lem_5_28
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:16.901192+00:00
-- url     : https://prove2.me/submissions/edc2004f-884e-4abf-bac6-33552760ece7

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent

-- ===== OddOrder/Isaacs/Ch05_Transfer/Main.lean =====
open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **N = S · C 補題**: `S : Sylow p N`, `C ⊴ N` で `N/C` が p-group ⇒
`(S : Subgroup N) ⊔ C = ⊤`.

**証明**: `mk' C : N →* N/C` 全射. `S.mapSurjective mk' surj : Sylow p (N/C)`.
`N/C` は p-group なので任意 Sylow p = ⊤ (cardinality 一致). よって
`S.map (mk' C) = ⊤`. `comap_map_eq` で `S ⊔ ker (mk' C) = S ⊔ C = ⊤`. -/
private lemma sylow_sup_normal_eq_top_of_quot_isPGroup
    {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    {C : Subgroup N} [C.Normal] (hQ : IsPGroup p (N ⧸ C))
    (S : Sylow p N) :
    (S : Subgroup N) ⊔ C = ⊤ := by
  have hSurj : Function.Surjective (QuotientGroup.mk' C : N →* N ⧸ C) :=
    QuotientGroup.mk'_surjective C
  let S' : Sylow p (N ⧸ C) := S.mapSurjective hSurj
  -- (S' : Subgroup (N ⧸ C)) = ⊤ via cardinality
  have h_S'_top : (S' : Subgroup (N ⧸ C)) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [S'.card_eq_multiplicity]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hk, Nat.factorization_pow_self Fact.out]
  -- Translate back: S ⊔ C = ⊤
  have h_S_map : (S : Subgroup N).map (QuotientGroup.mk' C) = ⊤ := h_S'_top
  have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' C) (S : Subgroup N)
  rw [h_S_map, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

/-- **"Normalizers grow" in p-group** (mathlib `lt_normalizer_of_isNilpotent_of_lt_top` の
p-group 特殊化). `G` finite p-group, `H : Subgroup G` で `H < ⊤` ⇒
`H < Subgroup.normalizer (H : Set G)`. -/
private lemma lt_normalizer_of_pgroup_of_lt_top
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {H : Subgroup G} (hH : H < ⊤) :
    H < Subgroup.normalizer (H : Set G) := by
  have : Group.IsNilpotent G := IsPGroup.isNilpotent hG
  exact OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top hH

/-- **Isaacs Lem 5.28**: 仮定「∀ p-subgroup `X` ⊆ `G`, `N_G(X)/C_G(X)` は p-group」
⇒ 任意 `P, Q : Sylow p G` で `Q = P^c` (= `c • Q = P` in mathlib 流) を満たす
`c ∈ C_G(P ⊓ Q)` が存在. **Frobenius normal p-complement 5.26 の鍵補題**.

**証明** (Isaacs p.174-175): `D := P ⊓ Q` の cardinality に関する強帰納法 (counter-example
の最大 `|D|` を取る). `D < P, D < Q` (else `P = Q`, `c = 1`).
* `N := N_G(D)`, `C := C_G(D)`, 仮定で `N/C` は p-group.
* `P ⊓ N = N_P(D) > D` (`IsPGroup.lt_normalizer_subgroupOf`).
* `S := Sylow p N ⊇ P ⊓ N`, `T := Sylow p N ⊇ Q ⊓ N`, `R := Sylow p G ⊇ S`.
* `N = S · C` (`sylow_sup_normal_eq_top_of_quot_isPGroup`).
* Sylow II in `N`: `T = n • S`, `n = s · y`, `s ∈ S`, `y ∈ C` ⇒ `T = y • S ⊆ y • R = R^y`.
* `P ⊓ R ⊇ P ⊓ N > D` ⇒ IH on `(P, R)`: `∃ x ∈ C_G(P ⊓ R), x • R = P`. `x` centralizes `D`.
* `R^y ⊓ Q ⊇ T ⊓ Q ⊇ Q ⊓ N > D` ⇒ IH on `(R^y, Q)`: `∃ z ∈ C_G(R^y ⊓ Q), z • Q = R^y`.
  `z` centralizes `D`.
* `(x y z) • Q = x • y • z • Q = x • (y • R^y) = x • R = P`. `x, y, z` all centralize `D`,
  hence `xyz ∈ C_G(D)`. 完了.

**実装状態**: ⭐ sorry-free. 助補題 (`sylow_sup_normal_eq_top_of_quot_isPGroup` +
`IsPGroup.lt_normalizer_subgroupOf`) と本体 (`(P ⊓ Q).index` に関する強帰納) とも完成済.

**FT クリティカル**: Frobenius 5.26 (3⇒1) 経由. -/
theorem _root_.solution [Finite G] {p : ℕ} [Fact p.Prime]
    (hH : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P Q : Sylow p G) :
    ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
      c • Q = P := by
  -- Strong induction on `k = ((P : Subgroup G) ⊓ Q).index`. Smaller k = larger intersection.
  suffices h : ∀ k : ℕ, ∀ (P Q : Sylow p G),
      ((P : Subgroup G) ⊓ (Q : Subgroup G)).index = k →
      ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
        c • Q = P by exact h _ P Q rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P Q hk
    -- **Case 1**: P = Q. Take c = 1.
    by_cases hPQ : P = Q
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hPQ, one_smul]
    -- **Case 2**: P ≠ Q. Apply textbook argument.
    · -- D := P ⊓ Q. P ≠ Q + Sylow card equality ⇒ D < P, D < Q.
      set D : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G) with hD_def
      have hPQ_card_eq : Nat.card ↥(P : Subgroup G) = Nat.card ↥(Q : Subgroup G) := by
        rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
      have hD_lt_P : D < (P : Subgroup G) := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h_eq
        have hP_le_Q : (P : Subgroup G) ≤ (Q : Subgroup G) := h_eq ▸ inf_le_right
        have h_subgroup_eq : (P : Subgroup G) = (Q : Subgroup G) :=
          Subgroup.eq_of_le_of_card_ge hP_le_Q hPQ_card_eq.symm.le
        exact hPQ (Sylow.ext h_subgroup_eq)
      have hD_lt_Q : D < (Q : Subgroup G) := by
        refine lt_of_le_of_ne inf_le_right ?_
        intro h_eq
        have hQ_le_P : (Q : Subgroup G) ≤ (P : Subgroup G) := h_eq ▸ inf_le_left
        have h_subgroup_eq : (P : Subgroup G) = (Q : Subgroup G) :=
          (Subgroup.eq_of_le_of_card_ge hQ_le_P hPQ_card_eq.le).symm
        exact hPQ (Sylow.ext h_subgroup_eq)
      -- N := normalizer D, C := centralizer D
      set N : Subgroup G := Subgroup.normalizer (D : Set G) with hN_def
      set C : Subgroup G := Subgroup.centralizer (D : Set G) with hC_def
      -- D ≤ N (le_normalizer), D ≤ P (already), D ≤ Q (already), D ≤ C (D centralizes itself? NO!)
      -- D centralizes itself only if D is abelian. Skip — we don't need D ≤ C.
      have hD_le_N : D ≤ N := Subgroup.le_normalizer
      have hD_le_P : D ≤ (P : Subgroup G) := inf_le_left
      have hD_le_Q : D ≤ (Q : Subgroup G) := inf_le_right
      -- D is p-group (subgroup of P p-group)
      have hD_pgroup : IsPGroup p ↥D := P.isPGroup'.to_le inf_le_left
      -- hH applied: ↥N ⧸ C.subgroupOf N is p-group
      have h_quot_pgroup : IsPGroup p (↥N ⧸ C.subgroupOf N) := hH D hD_pgroup
      -- **Step 1**: P ⊓ N > D via "normalizers grow" in ↥P
      have hPN_gt_D : D < (P : Subgroup G) ⊓ N := by
        have hD_sub_P_lt_top : D.subgroupOf (P : Subgroup G) < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          intro h_le; exact (not_le_of_gt hD_lt_P) h_le
        have h_lt_norm : D.subgroupOf (P : Subgroup G) <
            Subgroup.normalizer ((D.subgroupOf (P : Subgroup G)) : Set ↥(P : Subgroup G)) :=
          lt_normalizer_of_pgroup_of_lt_top P.isPGroup' hD_sub_P_lt_top
        have h_norm_eq : Subgroup.normalizer ((D.subgroupOf (P : Subgroup G)) :
            Set ↥(P : Subgroup G)) = N.subgroupOf (P : Subgroup G) :=
          (Subgroup.subgroupOf_normalizer_eq hD_le_P).symm
        rw [h_norm_eq] at h_lt_norm
        -- D.subgroupOf P < N.subgroupOf P (in ↥P). |·| translates to G.
        have h_card_lt : Nat.card ↥(D.subgroupOf (P : Subgroup G)) <
            Nat.card ↥(N.subgroupOf (P : Subgroup G)) := by
          have h_dvd := Subgroup.card_dvd_of_le h_lt_norm.le
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h_dvd) ?_
          intro hcardeq
          exact h_lt_norm.ne
            (Subgroup.eq_of_le_of_card_ge h_lt_norm.le hcardeq.symm.le)
        have h_card_D : Nat.card ↥(D.subgroupOf (P : Subgroup G)) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_P).toEquiv
        have h_card_NP : Nat.card ↥(N.subgroupOf (P : Subgroup G)) =
            Nat.card ↥((P : Subgroup G) ⊓ N) := by
          rw [show (P : Subgroup G) ⊓ N = N ⊓ (P : Subgroup G) from inf_comm _ _,
              ← Subgroup.subgroupOf_map_subtype]
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ ((P : Subgroup G).subtype_injective)).toEquiv
        rw [h_card_D, h_card_NP] at h_card_lt
        exact lt_of_le_of_ne (le_inf hD_le_P hD_le_N)
          (fun h => Nat.lt_irrefl _ (h ▸ h_card_lt))
      -- **Step 2**: Q ⊓ N > D (symmetric)
      have hQN_gt_D : D < (Q : Subgroup G) ⊓ N := by
        have hD_sub_Q_lt_top : D.subgroupOf (Q : Subgroup G) < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          intro h_le; exact (not_le_of_gt hD_lt_Q) h_le
        have h_lt_norm : D.subgroupOf (Q : Subgroup G) <
            Subgroup.normalizer ((D.subgroupOf (Q : Subgroup G)) : Set ↥(Q : Subgroup G)) :=
          lt_normalizer_of_pgroup_of_lt_top Q.isPGroup' hD_sub_Q_lt_top
        have h_norm_eq : Subgroup.normalizer ((D.subgroupOf (Q : Subgroup G)) :
            Set ↥(Q : Subgroup G)) = N.subgroupOf (Q : Subgroup G) :=
          (Subgroup.subgroupOf_normalizer_eq hD_le_Q).symm
        rw [h_norm_eq] at h_lt_norm
        have h_card_lt : Nat.card ↥(D.subgroupOf (Q : Subgroup G)) <
            Nat.card ↥(N.subgroupOf (Q : Subgroup G)) := by
          have h_dvd := Subgroup.card_dvd_of_le h_lt_norm.le
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h_dvd) ?_
          intro hcardeq
          exact h_lt_norm.ne
            (Subgroup.eq_of_le_of_card_ge h_lt_norm.le hcardeq.symm.le)
        have h_card_D : Nat.card ↥(D.subgroupOf (Q : Subgroup G)) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_Q).toEquiv
        have h_card_NQ : Nat.card ↥(N.subgroupOf (Q : Subgroup G)) =
            Nat.card ↥((Q : Subgroup G) ⊓ N) := by
          rw [show (Q : Subgroup G) ⊓ N = N ⊓ (Q : Subgroup G) from inf_comm _ _,
              ← Subgroup.subgroupOf_map_subtype]
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ ((Q : Subgroup G).subtype_injective)).toEquiv
        rw [h_card_D, h_card_NQ] at h_card_lt
        exact lt_of_le_of_ne (le_inf hD_le_Q hD_le_N)
          (fun h => Nat.lt_irrefl _ (h ▸ h_card_lt))
      -- **Step 3**: Sylow p of ↥N containing (P ⊓ N).subgroupOf N, (Q ⊓ N).subgroupOf N
      have hPN_pgroup_in_N : IsPGroup p ↥(((P : Subgroup G) ⊓ N).subgroupOf N) := by
        have h_iso : ((P : Subgroup G) ⊓ N).subgroupOf N ≃* ↥((P : Subgroup G) ⊓ N) :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (P.isPGroup'.to_le inf_le_left).of_equiv h_iso.symm
      have hQN_pgroup_in_N : IsPGroup p ↥(((Q : Subgroup G) ⊓ N).subgroupOf N) := by
        have h_iso : ((Q : Subgroup G) ⊓ N).subgroupOf N ≃* ↥((Q : Subgroup G) ⊓ N) :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (Q.isPGroup'.to_le inf_le_left).of_equiv h_iso.symm
      obtain ⟨S, hPN_le_S⟩ := IsPGroup.exists_le_sylow hPN_pgroup_in_N
      obtain ⟨T, hQN_le_T⟩ := IsPGroup.exists_le_sylow hQN_pgroup_in_N
      -- **Step 4**: R : Sylow p G containing S.map N.subtype
      set S_in_G : Subgroup G := (S : Subgroup ↥N).map N.subtype with hS_in_G_def
      have hS_in_G_pgroup : IsPGroup p ↥S_in_G := S.isPGroup'.map _
      obtain ⟨R, hS_in_G_le_R⟩ := IsPGroup.exists_le_sylow hS_in_G_pgroup
      -- **Step 5**: S ⊔ C.subgroupOf N = ⊤ in ↥N (via helper)
      have hS_sup_C : (S : Subgroup ↥N) ⊔ C.subgroupOf N = ⊤ :=
        sylow_sup_normal_eq_top_of_quot_isPGroup h_quot_pgroup S
      -- **Step 6**: Sylow II in ↥N: ∃ n : ↥N, n • S = T
      obtain ⟨n, hn_smul⟩ := MulAction.exists_smul_eq (↥N) S T
      -- **Step 7**: Decompose n = yC * sS (yC ∈ C.subgroupOf N, sS ∈ S)
      have hC_sup_S : C.subgroupOf N ⊔ (S : Subgroup ↥N) = ⊤ := by
        rw [sup_comm]; exact hS_sup_C
      have hn_in_top : (n : ↥N) ∈ C.subgroupOf N ⊔ (S : Subgroup ↥N) := by
        rw [hC_sup_S]; exact Subgroup.mem_top _
      obtain ⟨yC, hyC_in, sS, hsS_in, hn_eq⟩ := Subgroup.mem_sup_of_normal_left.mp hn_in_top
      -- **Step 8**: T = yC • S (since (yC * sS) • S = yC • (sS • S) = yC • S)
      have h_sS_S : (sS : ↥N) • S = S := by
        rw [Sylow.smul_eq_iff_mem_normalizer]; exact Subgroup.le_normalizer hsS_in
      have h_T_eq : T = yC • S := by
        rw [← hn_smul, ← hn_eq, mul_smul, h_sS_S]
      -- **Step 10 preview**: index strict inequality for IH (works for any subgroup > D).
      -- P ⊓ R ≥ P ⊓ N (via S_in_G ≤ R and P ⊓ N ⊆ S_in_G), and P ⊓ N > D.
      have hPN_le_S_in_G : (P : Subgroup G) ⊓ N ≤ S_in_G := by
        intro x hx
        have ⟨_, hx_N⟩ := Subgroup.mem_inf.mp hx
        refine ⟨⟨x, hx_N⟩, ?_, rfl⟩
        exact hPN_le_S (by rw [Subgroup.mem_subgroupOf]; exact hx)
      have hPN_le_R : (P : Subgroup G) ⊓ N ≤ (R : Subgroup G) :=
        hPN_le_S_in_G.trans hS_in_G_le_R
      have hPR_gt_D : D < (P : Subgroup G) ⊓ R :=
        lt_of_lt_of_le hPN_gt_D (le_inf inf_le_left hPN_le_R)
      -- **Step 9**: yR := yC.val • R (Sylow in G). Q ⊓ N ≤ yR.
      set yR : Sylow p G := (yC : G) • R with hyR_def
      have hQN_le_yR : (Q : Subgroup G) ⊓ N ≤ (yR : Subgroup G) := by
        intro q hq
        obtain ⟨hq_Q, hq_N⟩ := Subgroup.mem_inf.mp hq
        let q_N : ↥N := ⟨q, hq_N⟩
        have hq_N_in_QN : q_N ∈ ((Q : Subgroup G) ⊓ N).subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.mpr ⟨hq_Q, hq_N⟩
        have hq_N_in_T : q_N ∈ (T : Subgroup ↥N) := hQN_le_T hq_N_in_QN
        have hq_in_yCS : q_N ∈ ((yC • S : Sylow p ↥N) : Subgroup ↥N) := by
          rw [← h_T_eq]; exact hq_N_in_T
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq_in_yCS
        -- hq_in_yCS : (MulAut.conj yC)⁻¹ • q_N ∈ S
        have hs_in_R : ((MulAut.conj yC)⁻¹ q_N : ↥N).val ∈ (R : Subgroup G) := by
          apply hS_in_G_le_R
          exact ⟨(MulAut.conj yC)⁻¹ q_N, hq_in_yCS, rfl⟩
        change q ∈ (((yC : G) • R : Sylow p G) : Subgroup G)
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        -- Goal: (MulAut.conj (yC : G))⁻¹ q ∈ (R : Subgroup G)
        -- Both sides equal (yC : G)⁻¹ * q * (yC : G); ((MulAut.conj yC)⁻¹ q_N).val computes same
        convert hs_in_R using 1
        simp only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv]
        rfl
      -- **Step 10**: index strict inequalities for IH (P, R) and (yR, Q)
      have hQyR_gt_D : D < (Q : Subgroup G) ⊓ yR :=
        lt_of_lt_of_le hQN_gt_D (le_inf inf_le_left hQN_le_yR)
      -- (P ⊓ R).index < k (D.index)
      have h_PR_idx_lt : ((P : Subgroup G) ⊓ R : Subgroup G).index < k := by
        rw [← hk]
        have h_dvd : ((P : Subgroup G) ⊓ R).index ∣ D.index :=
          Subgroup.index_dvd_of_le hPR_gt_D.le
        have h_D_idx_pos : 0 < D.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine lt_of_le_of_ne (Nat.le_of_dvd h_D_idx_pos h_dvd) ?_
        intro h_eq
        have h_card_eq : Nat.card ↥D = Nat.card ↥((P : Subgroup G) ⊓ R) := by
          have h1 := Subgroup.index_mul_card D
          have h2 := Subgroup.index_mul_card ((P : Subgroup G) ⊓ R)
          rw [h_eq] at h2
          exact Nat.eq_of_mul_eq_mul_left h_D_idx_pos (h1.trans h2.symm)
        exact hPR_gt_D.ne (Subgroup.eq_of_le_of_card_ge hPR_gt_D.le h_card_eq.ge)
      -- ((Q ⊓ yR)).index < k. Note inf_comm: Q ⊓ yR = yR ⊓ Q? Use Q ⊓ yR for symmetric IH.
      have h_QyR_idx_lt : ((Q : Subgroup G) ⊓ yR : Subgroup G).index < k := by
        rw [← hk]
        have h_dvd : ((Q : Subgroup G) ⊓ yR).index ∣ D.index :=
          Subgroup.index_dvd_of_le hQyR_gt_D.le
        have h_D_idx_pos : 0 < D.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine lt_of_le_of_ne (Nat.le_of_dvd h_D_idx_pos h_dvd) ?_
        intro h_eq
        have h_card_eq : Nat.card ↥D = Nat.card ↥((Q : Subgroup G) ⊓ yR) := by
          have h1 := Subgroup.index_mul_card D
          have h2 := Subgroup.index_mul_card ((Q : Subgroup G) ⊓ yR)
          rw [h_eq] at h2
          exact Nat.eq_of_mul_eq_mul_left h_D_idx_pos (h1.trans h2.symm)
        exact hQyR_gt_D.ne (Subgroup.eq_of_le_of_card_ge hQyR_gt_D.le h_card_eq.ge)
      -- **Step 11**: IH applications + combine c = x · yC.val⁻¹ · z
      -- IH on (P, R): (P : Subgroup G) ⊓ R as intersection (need to match shape)
      -- The IH wants ∃ c ∈ centralizer((P' ⊓ Q' : Set G)), c • Q' = P' for any P' Q' pair with
      -- index of P' ⊓ Q' < k. Apply to (P, R) and (yR, Q).
      obtain ⟨x, hx_C, hxR⟩ := ih _ h_PR_idx_lt P R rfl
      -- hx_C : x ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (R : Subgroup G)) : Set G)
      -- hxR : x • R = P
      -- For (yR, Q): index = (yR : Subgroup G) ⊓ Q. Hmm I have Q ⊓ yR.
      have hyRQ_inf_eq : (yR : Subgroup G) ⊓ Q = (Q : Subgroup G) ⊓ yR := inf_comm _ _
      have h_yRQ_idx_lt' : ((yR : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G).index < k := by
        rw [hyRQ_inf_eq]; exact h_QyR_idx_lt
      obtain ⟨z, hz_C, hzQ⟩ := ih _ h_yRQ_idx_lt' yR Q rfl
      -- hz_C : z ∈ Subgroup.centralizer (((yR : Subgroup G) ⊓ (Q : Subgroup G)) : Set G)
      -- hzQ : z • Q = yR
      -- c := x * yC.val⁻¹ * z
      refine ⟨x * (yC : G)⁻¹ * z, ?_, ?_⟩
      · -- c ∈ centralizer D
        have hyC_cent_D : (yC : G) ∈ Subgroup.centralizer (D : Set G) := by
          have : yC.val ∈ C := by
            have := hyC_in
            rwa [Subgroup.mem_subgroupOf] at this
          exact this
        have hyC_inv_cent_D : ((yC : G))⁻¹ ∈ Subgroup.centralizer (D : Set G) :=
          (Subgroup.centralizer (D : Set G)).inv_mem hyC_cent_D
        have hx_cent_D : x ∈ Subgroup.centralizer (D : Set G) := by
          have h_D_le : (D : Set G) ⊆ (((P : Subgroup G) ⊓ R : Subgroup G) : Set G) := by
            intro a ha
            exact Subgroup.mem_inf.mpr
              ⟨hD_le_P ha, hPN_le_R (le_inf hD_le_P hD_le_N ha)⟩
          exact Subgroup.centralizer_le h_D_le hx_C
        have hz_cent_D : z ∈ Subgroup.centralizer (D : Set G) := by
          have h_D_le : (D : Set G) ⊆ (((yR : Subgroup G) ⊓ Q : Subgroup G) : Set G) := by
            intro a ha
            refine Subgroup.mem_inf.mpr ⟨?_, hD_le_Q ha⟩
            -- a ∈ yR = yC.val • R; yC centralizes D so yC⁻¹ a yC = a ∈ R
            change a ∈ (((yC : G) • R : Sylow p G) : Subgroup G)
            rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
            have h_a_in_R : a ∈ (R : Subgroup G) :=
              hPN_le_R (le_inf hD_le_P hD_le_N ha)
            have h_comm : a * (yC : G) = (yC : G) * a :=
              Subgroup.mem_centralizer_iff.mp hyC_cent_D a ha
            have h_smul_eq : (MulAut.conj (yC : G))⁻¹ • a = a := by
              change (yC : G)⁻¹ * a * (yC : G) = a
              rw [mul_assoc, h_comm, ← mul_assoc, inv_mul_cancel, one_mul]
            rw [h_smul_eq]; exact h_a_in_R
          exact Subgroup.centralizer_le h_D_le hz_C
        exact (Subgroup.centralizer (D : Set G)).mul_mem
          ((Subgroup.centralizer (D : Set G)).mul_mem hx_cent_D hyC_inv_cent_D)
          hz_cent_D
      · -- c • Q = P
        -- z • Q = yR = yC.val • R, so yC.val⁻¹ • (z • Q) = R, (yC.val⁻¹ * z) • Q = R
        -- x • R = P, so x • ((yC.val⁻¹ * z) • Q) = P, (x * yC.val⁻¹ * z) • Q = P
        rw [show (x * (yC : G)⁻¹ * z) • Q = x • ((yC : G)⁻¹ • (z • Q)) by
          rw [← mul_smul, ← mul_smul]]
        rw [hzQ, hyR_def]
        rw [show ((yC : G)⁻¹ • (yC : G) • R : Sylow p G) = R from by
          rw [← mul_smul, inv_mul_cancel, one_smul]]
        exact hxR

end

end OddOrder.Isaacs.Ch05
