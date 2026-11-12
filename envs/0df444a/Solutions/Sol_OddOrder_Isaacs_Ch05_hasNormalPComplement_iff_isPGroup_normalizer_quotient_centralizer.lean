-- Prove2me | solution 1 for OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:35:47.375351+00:00
-- url     : https://prove2.me/submissions/5b4cc0d3-f8a7-4b14-9c66-28b43e57bc84

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
import Theorems.Thm_OddOrder_Isaacs_Ch05_OPrime_index_isPGroup
import Theorems.Thm_OddOrder_Isaacs_Ch05_isaacs_lem_5_28
import Theorems.Thm_OddOrder_Isaacs_Ch05_OPrime_meet_sylow_eq_bot_of_controlsOwnFusion
import Theorems.Thm_OddOrder_Isaacs_Ch05_isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement

-- ===== OddOrder/Isaacs/Ch05_Transfer/Main.lean =====
open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **Isaacs Thm 5.25 (⇒)**: G has normal p-complement ⇒ any Sylow_p `P` controls own fusion.

**証明** (Isaacs p.173): 与えられた N normal p-comp で `G = N · P`, `N ⊓ P = ⊥`.
x, y ∈ P G-conjugate: ∃ g, g x g⁻¹ = y. `mem_sup_of_normal_left` で `g = n · p`
(n ∈ N, p ∈ P). z := p x p⁻¹ ∈ P. `g x g⁻¹ = n z n⁻¹ = y ∈ P`. 一方
`n z n⁻¹ · z⁻¹ = n · (z n⁻¹ z⁻¹) ∈ N` (N normal) かつ `∈ P` (= y · z⁻¹). よって
`∈ N ⊓ P = ⊥`, つまり `n z n⁻¹ = z = p x p⁻¹ = y`. `u = p` で完了. -/
theorem controlsOwnFusion_of_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hG : HasNormalPComplement p G) :
    P.ControlsOwnFusion := by
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  have : N.Normal := hN_normal
  rintro x y hx_P hy_P ⟨g, hgxy⟩
  -- g ∈ N ⊔ P = ⊤ ⇒ g = n · p (n ∈ N, p ∈ P)
  have h_sup_top : N ⊔ (P : Subgroup G) = ⊤ := (hN_compl P).sup_eq_top
  have hg_in_sup : g ∈ N ⊔ (P : Subgroup G) := h_sup_top ▸ Subgroup.mem_top g
  obtain ⟨n, hn_N, q, hq_P, hg_eq⟩ := Subgroup.mem_sup_of_normal_left.mp hg_in_sup
  -- z := q * x * q⁻¹ ∈ P
  have hz_P : q * x * q⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hq_P hx_P)
      ((P : Subgroup G).inv_mem hq_P)
  -- y = g x g⁻¹ = n · (q x q⁻¹) · n⁻¹ = n z n⁻¹
  have h_y_eq : y = n * (q * x * q⁻¹) * n⁻¹ := by
    rw [← hgxy, ← hg_eq]; group
  -- n z n⁻¹ ∈ P (= y)
  have h_nzn_in_P : n * (q * x * q⁻¹) * n⁻¹ ∈ (P : Subgroup G) := h_y_eq ▸ hy_P
  -- n z n⁻¹ · z⁻¹ ∈ N: rewrite as n · (z n⁻¹ z⁻¹) with z n⁻¹ z⁻¹ ∈ N (conj)
  have h_in_N : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N := by
    have hzn_inv_z_inv_N : (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N :=
      hN_normal.conj_mem n⁻¹ (N.inv_mem hn_N) (q * x * q⁻¹)
    have heq : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ =
               n * ((q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹) := by group
    rw [heq]
    exact N.mul_mem hn_N hzn_inv_z_inv_N
  -- n z n⁻¹ · z⁻¹ ∈ P
  have h_in_P : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem h_nzn_in_P ((P : Subgroup G).inv_mem hz_P)
  -- n z n⁻¹ · z⁻¹ ∈ N ⊓ P = ⊥, so equal to 1
  have h_eq_one : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ = 1 := by
    have h_in_inf : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N ⊓ (P : Subgroup G) :=
      ⟨h_in_N, h_in_P⟩
    rw [(hN_compl P).disjoint.eq_bot, Subgroup.mem_bot] at h_in_inf
    exact h_in_inf
  -- n z n⁻¹ = z, so y = z = q x q⁻¹
  rw [mul_inv_eq_one] at h_eq_one
  refine ⟨q, hq_P, ?_⟩
  rw [h_y_eq, h_eq_one]

/-- **Isaacs Thm 5.25 (⇐)**: any Sylow_p `P` controls own fusion ⇒ G has normal p-complement.

**証明** (Isaacs p.173, harder direction): `N := OPrime p G`. 主な仕事は
`(P : Subgroup G) ⊓ N = ⊥` を示すことで, これが
`OPrime_meet_sylow_eq_bot_of_controlsOwnFusion` (前置の helper). 残りは:
(B) Sylow II + N normal で任意 Sylow `R` に拡張 (`g • (P ⊓ N) = (g • P) ⊓ N`). ✅
(C) p ∤ |N| (任意 Sylow R で R ⊓ N = ⊥ + Cauchy 矛盾) → `|N| · |P'| = |G|` +
    `Nat.Coprime (|N|) (p^a)` → `Subgroup.isComplement'_of_coprime`. ✅

**実装状態 (2026-05-25)**: Step A (heart) + Steps B/C 完成 (sorry-free). -/
theorem hasNormalPComplement_of_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    HasNormalPComplement p G := by
  -- Set N := OPrime p G, the normal-p-complement witness.
  set N : Subgroup G := OPrime p G with hN_def
  have hN_normal : N.Normal := inferInstance
  -- |G : N| is a p-power, say p^a.
  obtain ⟨a, hN_idx_pow⟩ := OPrime_index_isPGroup p G
  -- **Step A** (heart, deferred to helper): `(P : Subgroup G) ⊓ N = ⊥`.
  have h_PN_bot : (P : Subgroup G) ⊓ N = ⊥ :=
    OPrime_meet_sylow_eq_bot_of_controlsOwnFusion P hP
  -- **Step B**: Conjugation propagates Step A to every Sylow `R` (Sylow II + N normal):
  -- ∃ g, g • P = R. Then `(R ⊓ N) = (g • P) ⊓ (g • N) = g • (P ⊓ N) = g • ⊥ = ⊥`.
  have h_all_sylow : ∀ R : Sylow p G, (R : Subgroup G) ⊓ N = ⊥ := fun R => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
    have h_R_eq : (R : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    have h_N_eq : MulAut.conj g • N = N := Subgroup.Normal.conj_smul_eq_self g N
    calc (R : Subgroup G) ⊓ N
        = MulAut.conj g • (P : Subgroup G) ⊓ N := by rw [h_R_eq]
      _ = MulAut.conj g • (P : Subgroup G) ⊓ MulAut.conj g • N := by rw [h_N_eq]
      _ = MulAut.conj g • ((P : Subgroup G) ⊓ N) := (Subgroup.smul_inf _ _ _).symm
      _ = MulAut.conj g • (⊥ : Subgroup G) := by rw [h_PN_bot]
      _ = ⊥ := Subgroup.smul_bot _
  -- **Step C**: `p ∤ |N|` (any p-element in N would lie in some Sylow R, hence in R ⊓ N = ⊥)
  -- ⇒ `|N| · p^c = |G|` where `c = (|G|).factorization p` ⇒ `c = a` ⇒ `|N| · |P'| = |G|`
  -- + disjoint ⇒ `IsComplement' N P'`.
  refine ⟨N, hN_normal, fun P' => ?_⟩
  have h_P'N_bot : (P' : Subgroup G) ⊓ N = ⊥ := h_all_sylow P'
  -- C.1: p ∤ |N|
  have h_p_ndvd_N : ¬ p ∣ Nat.card ↥N := by
    intro hp_dvd
    obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hp_dvd
    have hx_ne : (x : ↥N) ≠ 1 := by
      intro h; rw [h, orderOf_one] at hx_order
      exact (Fact.out : p.Prime).one_lt.ne hx_order
    -- (x : G) has the same order p (Subgroup.orderOf_coe)
    have hx_order_G : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx_order
    -- ⟨x.val⟩ as Subgroup G is a p-group (cyclic of order p)
    have hpg : IsPGroup p (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card ((Nat.card_zpowers (x : G)).trans hx_order_G |>.trans (pow_one p).symm)
    obtain ⟨Q, hQ_le⟩ := hpg.exists_le_sylow
    have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ_le (Subgroup.mem_zpowers _)
    have hxN : (x : G) ∈ N := x.property
    have h_in : (x : G) ∈ (Q : Subgroup G) ⊓ N := ⟨hxQ, hxN⟩
    rw [h_all_sylow Q, Subgroup.mem_bot] at h_in
    exact hx_ne (Subtype.ext h_in)
  -- C.2: factorization of |G| at p = a
  have h_fact_a : (Nat.card G).factorization p = a := by
    have hN_card_mul : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
    have h_total : Nat.card G = Nat.card ↥N * p ^ a := by rw [← hN_card_mul, hN_idx_pow]
    rw [h_total, Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne'
      (pow_pos (Fact.out : p.Prime).pos a).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_N,
      Nat.Prime.factorization_pow (Fact.out : p.Prime),
      Finsupp.single_apply]
    simp
  -- C.3: |P'| = p^a, hence |N| · |P'| = |G|
  have hP'_card : Nat.card ↥(P' : Subgroup G) = p ^ a := by
    rw [P'.card_eq_multiplicity, h_fact_a]
  have h_card_mul : Nat.card ↥N * Nat.card ↥(P' : Subgroup G) = Nat.card G := by
    rw [hP'_card, ← hN_idx_pow]; exact Subgroup.card_mul_index N
  -- C.4: Coprime |N| |P'|
  have h_coprime : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(P' : Subgroup G)) := by
    rw [hP'_card]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_N).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_card_mul h_coprime

/-- **Isaacs Thm 5.25**: G has normal p-complement ⇔ Sylow_p controls own fusion. -/
theorem hasNormalPComplement_iff_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    HasNormalPComplement p G ↔ P.ControlsOwnFusion :=
  ⟨controlsOwnFusion_of_hasNormalPComplement P, hasNormalPComplement_of_controlsOwnFusion P⟩

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

/-- **Isaacs Thm 5.26 Frobenius normal p-complement** ⭐ **FT クリティカル**.
`G` has normal p-complement ⇔ ∀ p-subgroup `X`, `N_G(X)/C_G(X)` is p-group.

**証明** (Isaacs p.175-177):
* (1) ⇒ (3): `hasNormalPComplement_of_subgroup` (Lem 5.27 Part 1) で
  ∀ p-subgroup X non-trivial, `normalizer X` も normal p-comp を持つ.
  `isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`
  (Lem 5.27 Part 2) で結論. ✅
* (3) ⇒ (1): 任意 Sylow `P` で `P.ControlsOwnFusion` を示し (Lem 5.28 経由),
  `hasNormalPComplement_of_controlsOwnFusion` (Thm 5.25 ⇐) で normal p-comp. ✅ -/
theorem _root_.solution
    [Finite G] {p : ℕ} [Fact p.Prime] :
    HasNormalPComplement p G ↔
    ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  refine ⟨fun hG X hXp => ?_, fun hH => ?_⟩
  · -- (1) ⇒ (3): via Lem 5.27 Part 1 + Part 2 (both sorry-free)
    exact isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
      (fun Y _hY_ne _hY_pg => hasNormalPComplement_of_subgroup hG
        (Subgroup.normalizer (Y : Set G)))
      X hXp
  · -- (3) ⇒ (1): Pick Sylow P, show P.ControlsOwnFusion via Lem 5.28,
    -- then apply Thm 5.25 (⇐).
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
    refine (hasNormalPComplement_iff_controlsOwnFusion P).mpr ?_
    intro x y hx_P hy_P ⟨g, hgxy⟩
    -- Apply Lem 5.28 to (P, g • P)
    set gP : Sylow p G := g • P with hgP_def
    -- y ∈ P ⊓ gP
    have hy_in_gP : y ∈ (gP : Subgroup G) := by
      change y ∈ ((g • P : Sylow p G) : Subgroup G)
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have h_smul_eq : (MulAut.conj g)⁻¹ • y = x := by
        change g⁻¹ * y * g = x
        rw [← hgxy]; group
      rw [h_smul_eq]; exact hx_P
    have hy_in_PgP : y ∈ (P : Subgroup G) ⊓ (gP : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨hy_P, hy_in_gP⟩
    -- Lem 5.28: ∃ c ∈ C(P ⊓ gP), c • gP = P
    obtain ⟨c, hc_C, hc_smul⟩ := isaacs_lem_5_28 hH P gP
    -- c centralizes y
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hc_C y hy_in_PgP).symm
    -- cg ∈ N(P): c • gP = P ⇒ (c * g) • P = P ⇒ cg ∈ normalizer
    have hcg_in_N : c * g ∈ Subgroup.normalizer (P : Set G) := by
      rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, ← hgP_def]
      exact hc_smul
    set N_P : Subgroup G := Subgroup.normalizer (P : Set G) with hN_P_def
    -- P ≤ N(P) (general)
    have hP_le_N : (P : Subgroup G) ≤ N_P := Subgroup.le_normalizer
    -- P as Sylow of ↥N(P)
    let P_NP : Sylow p ↥N_P := P.subtype hP_le_N
    -- hH applied to P: ↥N(P) / C(P).subgroupOf N(P) is p-group
    have h_quot_pgroup : IsPGroup p
        (↥N_P ⧸ (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P) :=
      hH P P.isPGroup'
    -- Normal instance for the centralizer subgroupOf
    have : ((Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P).Normal :=
      centralizer_subgroupOf_normalizer_normal (P : Subgroup G)
    -- N(P) = C(P).subgroupOf N(P) ⊔ P_NP (via helper applied to ↥N(P))
    have hSC_top : (P_NP : Subgroup ↥N_P) ⊔
        (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P = ⊤ :=
      sylow_sup_normal_eq_top_of_quot_isPGroup h_quot_pgroup P_NP
    -- cg lifted to ↥N(P)
    let cg_N : ↥N_P := ⟨c * g, hcg_in_N⟩
    have hcg_in_sup : cg_N ∈ (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P
        ⊔ (P_NP : Subgroup ↥N_P) := by
      rw [sup_comm]; rw [hSC_top]; exact Subgroup.mem_top _
    obtain ⟨t_N, ht_C, u_N, hu_P, htu_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hcg_in_sup
    -- t_N : ↥N(P), t_N ∈ centralizer.subgroupOf ⇒ t_N.val ∈ centralizer P
    -- u_N : ↥N(P), u_N ∈ P_NP ⇒ u_N.val ∈ P
    have ht_in_C : (t_N : G) ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      have := ht_C
      rwa [Subgroup.mem_subgroupOf] at this
    have hu_in_P : (u_N : G) ∈ (P : Subgroup G) := by
      have := hu_P
      change (u_N : G) ∈ (P : Subgroup G) at this ⊢
      exact this
    -- (cg).val = t_N.val * u_N.val
    have hcg_val_eq : c * g = (t_N : G) * (u_N : G) := by
      have h := congrArg Subtype.val htu_eq
      exact h.symm
    -- y = (cg) • x = (t_N.val * u_N.val) • x = t_N.val • (u_N.val • x) = u_N.val • x (t centralizes
    -- uxu⁻¹ ∈ P)
    refine ⟨(u_N : G), hu_in_P, ?_⟩
    -- Goal: u_N.val * x * u_N.val⁻¹ = y
    -- First: y = (cg) x (cg)⁻¹. From c * y = y * c, y = c y c⁻¹ = c (g x g⁻¹) c⁻¹ = (cg) x (cg)⁻¹.
    have h_y_eq_cgx : y = (c * g) * x * (c * g)⁻¹ := by
      have h_c_y_eq : c * y * c⁻¹ = y := by
        rw [hcy]; group
      calc y = c * y * c⁻¹ := h_c_y_eq.symm
        _ = c * (g * x * g⁻¹) * c⁻¹ := by rw [hgxy]
        _ = (c * g) * x * (c * g)⁻¹ := by group
    -- (cg) x (cg)⁻¹ = (t * u) x (t * u)⁻¹. Use t centralizes uxu⁻¹ ∈ P to simplify.
    have h_uux_in_P : (u_N : G) * x * (u_N : G)⁻¹ ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem
        ((P : Subgroup G).mul_mem hu_in_P hx_P)
        ((P : Subgroup G).inv_mem hu_in_P)
    have h_t_comm : ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G) =
        (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp ht_in_C _ h_uux_in_P
    have h_t_uxu_eq : (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G)⁻¹ =
        (u_N : G) * x * (u_N : G)⁻¹ := by
      rw [← h_t_comm]; group
    calc (u_N : G) * x * (u_N : G)⁻¹
        = (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G)⁻¹ := h_t_uxu_eq.symm
      _ = ((t_N : G) * (u_N : G)) * x * ((t_N : G) * (u_N : G))⁻¹ := by group
      _ = (c * g) * x * (c * g)⁻¹ := by rw [← hcg_val_eq]
      _ = y := h_y_eq_cgx.symm

end

end OddOrder.Isaacs.Ch05
