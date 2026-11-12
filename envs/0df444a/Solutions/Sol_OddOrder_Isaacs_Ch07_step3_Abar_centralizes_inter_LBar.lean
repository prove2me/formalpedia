-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.step3_Abar_centralizes_inter_LBar
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:02.470704+00:00
-- url     : https://prove2.me/submissions/df27a615-f835-42cb-8cf8-d0dfd43895a3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_OddOrder_Isaacs_Ch07_oPiCorePrime_subgroup_eq_bot_of_opCore_le
import Theorems.Thm_OddOrder_Isaacs_Ch07_centralizer_center_sylow_subgroup_eq_self_of_intermediate

-- ===== OddOrder/GroupTheory/ThompsonSubgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

/-- `J(P) ≤ P`: Thompson subgroup は `P` の部分群. -/
theorem thompsonJ_le (P : Subgroup G) (p : ℕ) : thompsonJ P p ≤ P := by
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact hE.1

end Subgroup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `L.map (mk' U) = L̅`: the image of `L = O_{p',p}(G)` in `G̅ = G/U`
is exactly `L̅ = O_{p'}(G̅)`.  Follows from `map_comap_eq_self_of_surjective`. -/
theorem opPpPrimeCore_map_eq_LBar
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (opPpPrimeCore G p).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) =
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
  unfold opPpPrimeCore
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) _

/-- The image of an elementary abelian subgroup under a group hom is
elementary abelian.  Generic for `Subgroup.IsElementaryAbelian`. -/
theorem isElementaryAbelian_map_of_isElementaryAbelian
    {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    {A : Subgroup G} (hA : A.IsElementaryAbelian p) :
    (A.map f).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, a₁, ha₁, rfl⟩ ⟨_, a₂, ha₂, rfl⟩
    apply Subtype.ext
    change f a₁ * f a₂ = f a₂ * f a₁
    rw [← f.map_mul, ← f.map_mul]
    have hcomm : (⟨a₁, ha₁⟩ : A) * ⟨a₂, ha₂⟩ = ⟨a₂, ha₂⟩ * ⟨a₁, ha₁⟩ :=
      hA.1 ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
    exact congr_arg f (congr_arg Subtype.val hcomm)
  · rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    change (f a) ^ p = 1
    rw [← f.map_pow, ← f.map_one]
    have hpow : (⟨a, ha⟩ : A) ^ p = 1 := hA.2 ⟨a, ha⟩
    exact congr_arg f (congr_arg Subtype.val hpow)

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 3** (mmd L3850-3856): the IH-consuming core of the
Goldschmidt argument.

Given `U·A ≤ H` with `H` a **proper** subgroup of `G` and `H ∩ P ∈ Syl_p(H)`,
the conclusion is `⁅L ⊓ H, A⁆ ≤ U`, i.e. `Ā` centralizes `(L ∩ H)bar` in
`Ḡ = G/U`.  Here `L = O_{p',p}(G)` (`opPpPrimeCore`), `U = O_p(G)`.

Book proof (mmd L3850-3856):
* `H` satisfies the five Thm 7.6 hypotheses: (i) `p`-separable (subgroup),
  (ii) `p ≠ 2`, (iii) Sylow-2 abelian (descent), (iv) `O_{p'}(H) = 1`
  (`oPiCorePrime_subgroup_eq_bot_of_opCore_le`, landed), and (v)
  `C_H(Z(S)) = S` for `S = H ∩ P`
  (`centralizer_center_sylow_subgroup_eq_self_of_intermediate`, landed).
* By the IH (`H < G`), `J(S) ⊴ H`.  Since `A ∈ E(P)` and `A ⊆ S ⊆ P`,
  `A ∈ E(S)`, so `A ⊆ J(S)`.
* `⁅L ⊓ H, A⁆ ⊆ ⁅L ⊓ H, J(S)⁆ ⊆ (L ⊓ H) ⊓ J(S)` (both normal in `H`)
  `⊆ L ⊓ J(S) ⊆ U` (`U` is the unique Sylow-`p` of `L`).

Hypothesis (v) is the landed
`centralizer_center_sylow_subgroup_eq_self_of_intermediate`. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (_hp2 : p ≠ 2)
    (h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    (ih : ∀ (H : Type u) [Group H] [Finite H]
      [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H],
      Nat.card H < Nat.card G →
      (∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) →
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} H = ⊥ →
      ∀ (Q : Sylow p H),
        Subgroup.centralizer
            (((Subgroup.center (Q : Subgroup H)).map
              (Q : Subgroup H).subtype) : Set H)
          = (Q : Subgroup H) →
        (Subgroup.thompsonJ (Q : Subgroup H) p).Normal)
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    {H : Subgroup G}
    (hH_ne_top : H ≠ ⊤)
    (hUA_le_H : OddOrder.Isaacs.Ch01.opCore p G ⊔ A ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    (⁅opPpPrimeCore G p ⊓ H, A⁆ : Subgroup G) ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  have hU_le_H : U ≤ H := le_sup_left.trans hUA_le_H
  have hA_le_H : A ≤ H := le_sup_right.trans hUA_le_H
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  -- `S` mapped to `G` is `H ⊓ P`.
  have hS_map : (S : Subgroup ↥H).map H.subtype = H ⊓ (P : Subgroup G) := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  -- (a) `Nat.card ↥H < Nat.card G` (since `H ≠ ⊤`).
  have hcard_lt : Nat.card ↥H < Nat.card G := by
    have hidx : 1 < H.index := Subgroup.one_lt_index_of_ne_top hH_ne_top
    have hmul : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
    calc Nat.card ↥H = Nat.card ↥H * 1 := (mul_one _).symm
      _ < Nat.card ↥H * H.index := (Nat.mul_lt_mul_left Nat.card_pos).mpr hidx
      _ = Nat.card G := hmul
  -- (b) Descend hypotheses to `↥H`.
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (↥H) :=
    OddOrder.Isaacs.Ch03.Subgroup.isPiSeparable_of_isPiSeparable ({p} : Set ℕ) H
  have h2abelian' : ∀ T : Subgroup ↥H, IsPGroup 2 T → ∀ x y : ↥T, x * y = y * x := by
    intro T hT2
    have hTG2 : IsPGroup 2 (T.map H.subtype) := hT2.map H.subtype
    have hTGcomm := h2abelian (T.map H.subtype) hTG2
    intro a b
    apply Subtype.ext; apply Subtype.ext
    have h := hTGcomm ⟨((a : ↥H) : G), ⟨(a : ↥H), a.property, rfl⟩⟩
      ⟨((b : ↥H) : G), ⟨(b : ↥H), b.property, rfl⟩⟩
    exact congrArg (fun z : ↥(T.map H.subtype) => (z : G)) h
  have h_oPi' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (↥H) = ⊥ :=
    oPiCorePrime_subgroup_eq_bot_of_opCore_le h_oPiPrime_trivial hU_le_H
  -- Hypothesis (v) for `S`.
  have hv : Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) :=
    centralizer_center_sylow_subgroup_eq_self_of_intermediate h_oPiPrime_trivial P
      h_centralizer_center hU_le_H S hS_eq
  -- (c) IH: `J(S) ⊴ ↥H`.
  have hJS_normal : (Subgroup.thompsonJ (S : Subgroup ↥H) p).Normal :=
    ih (↥H) hcard_lt h2abelian' h_oPi' S hv
  -- (d) `A.subgroupOf H ∈ maxElemAbelianIn S p`, hence `A.subgroupOf H ≤ J(S)`.
  have hAsub_le_S : A.subgroupOf H ≤ (S : Subgroup ↥H) := by
    rw [hS_eq]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.property, hA_le_P hx⟩
  -- `A.subgroupOf H ≃* A` (since `A ≤ H`), preserving cardinality and elem-ab.
  have hAsub_equiv := Subgroup.subgroupOfEquivOfLe hA_le_H
  have hAsub_card : Nat.card ↥(A.subgroupOf H) = Nat.card ↥A :=
    Nat.card_congr hAsub_equiv.toEquiv
  have hAsub_el : (A.subgroupOf H).IsElementaryAbelian p := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · exact hAsub_equiv.injective (by
        rw [map_mul, map_mul]; exact (hA_mem.2.1).comm (hAsub_equiv x) (hAsub_equiv y))
    · exact hAsub_equiv.injective (by
        rw [map_pow, map_one]; exact (hA_mem.2.1).pow_eq_one (hAsub_equiv x))
  have hAsub_mem : A.subgroupOf H ∈ Subgroup.maxElemAbelianIn (S : Subgroup ↥H) p := by
    refine ⟨hAsub_le_S, hAsub_el, ?_⟩
    intro F hF_S hF_el
    -- `F.map H.subtype ≤ H ⊓ P ≤ P` is elem-ab; `A ∈ E(P)` ⇒ `|F| ≤ |A|`.
    have hFmap_le_P : F.map H.subtype ≤ (P : Subgroup G) := by
      have : F.map H.subtype ≤ (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hF_S
      rw [hS_map] at this
      exact this.trans inf_le_right
    have hFmap_el : (F.map H.subtype).IsElementaryAbelian p :=
      isElementaryAbelian_map_of_isElementaryAbelian H.subtype hF_el
    have hFmap_card : Nat.card ↥(F.map H.subtype) = Nat.card ↥F :=
      Nat.card_congr (Subgroup.equivMapOfInjective F H.subtype Subtype.coe_injective).symm.toEquiv
    have hle := hA_mem.2.2 (F.map H.subtype) hFmap_le_P hFmap_el
    rw [hFmap_card] at hle
    rw [← hAsub_card] at hle
    exact hle
  have hAsub_le_JS : A.subgroupOf H ≤ Subgroup.thompsonJ (S : Subgroup ↥H) p :=
    Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn hAsub_mem
  -- (e) Commutator chain in `↥H`: `⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ U.subgroupOf H`.
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  -- `L.subgroupOf H` is normal in `↥H` (L ⊴ G).
  have hLsub_normal : (L.subgroupOf H).Normal := by
    rw [hL_def]; exact (opPpPrimeCore_normal (G := G) (p := p)).subgroupOf H
  -- `J(S) ≤ S ≤ P`, so `J(S).map H.subtype` is a `p`-subgroup of `G` inside `P`.
  have hJS_le_S : Subgroup.thompsonJ (S : Subgroup ↥H) p ≤ (S : Subgroup ↥H) :=
    Subgroup.thompsonJ_le _ _
  have hJSmap_le_P : (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤ (P : Subgroup G) := by
    have : (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
        (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hJS_le_S
    rw [hS_map] at this
    exact this.trans inf_le_right
  -- `⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ ⁅L.subgroupOf H, J(S)⁆ ≤ (L.subgroupOf H) ⊓ J(S)`.
  have := hJS_normal
  have hchain : (⁅L.subgroupOf H, A.subgroupOf H⁆ : Subgroup ↥H) ≤
      (L.subgroupOf H) ⊓ Subgroup.thompsonJ (S : Subgroup ↥H) p := by
    refine le_trans (Subgroup.commutator_mono le_rfl hAsub_le_JS) ?_
    exact Subgroup.commutator_le_inf (L.subgroupOf H) (Subgroup.thompsonJ (S : Subgroup ↥H) p)
  -- Map the chain back to `G`: `⁅L ⊓ H, A⁆ ≤ ((L.subgroupOf H) ⊓ J(S)).map H.subtype`.
  have hcomm_map_eq : (⁅L.subgroupOf H, A.subgroupOf H⁆ : Subgroup ↥H).map H.subtype =
      ⁅(L ⊓ H), A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA_le_H, inf_comm L H]
  -- The target `⁅L ⊓ H, A⁆ ≤ U`.
  have hgoal_map : ⁅(L ⊓ H), A⁆ ≤ ((L.subgroupOf H) ⊓
      Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype := by
    rw [← hcomm_map_eq]; exact Subgroup.map_mono hchain
  -- `((L.subgroupOf H) ⊓ J(S)).map H.subtype ≤ L ⊓ (J(S).map H.subtype)`.
  have hinf_map_le : ((L.subgroupOf H) ⊓ Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
      L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype := by
    rintro _ ⟨x, ⟨hxL, hxJ⟩, rfl⟩
    refine ⟨?_, Subgroup.mem_map_of_mem _ hxJ⟩
    have : (x : G) ∈ L := hxL
    exact this
  -- `L ⊓ (p-subgroup) ≤ U`: any `p`-subgroup of `L` lies in `U` (since `L/U` is `p'`).
  have hLinf_le_U : L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤ U := by
    -- `K := L ⊓ J(S).map` is a `p`-group (≤ J(S).map ≤ P).
    have hK_le_P : L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype ≤
        (P : Subgroup G) := inf_le_right.trans hJSmap_le_P
    have hK_pg : IsPGroup p ↥(L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype) :=
      P.isPGroup'.of_injective (Subgroup.inclusion hK_le_P) (Subgroup.inclusion_injective hK_le_P)
    -- `K ≤ L`, and `K.map mk` is a `p`-group inside `L̄ = O_{p'}(Ḡ)`, hence trivial ⇒ `K ≤ U`.
    intro x hx
    have hxL : x ∈ L := hx.1
    -- `mk x ∈ L̄` and `mk x` lies in the `p`-group image, but `L̄` is `p'`, so `mk x = 1`.
    have hKmap_pg : IsPGroup p ((L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map
        mk) :=
      hK_pg.map mk
    have hxbar_mem : mk x ∈ (L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk :=
      Subgroup.mem_map_of_mem mk hx
    have hxbar_Lbar : mk x ∈ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
      have hLmap : L.map mk = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
        rw [hL_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
      rw [← hLmap]; exact Subgroup.mem_map_of_mem mk hxL
    -- `mk x` has order a power of `p` (in the image) and divides `|L̄|` (a `p'`-number) ⇒
    -- `mk x = 1`.
    have hxbar_one : mk x = 1 := by
      -- order of `mk x` divides a `p`-power (from the `p`-group `K.map mk`).
      obtain ⟨k, hk⟩ := hKmap_pg ⟨mk x, hxbar_mem⟩
      have hord_dvd_pk : orderOf (mk x) ∣ p ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        have hk' : (⟨mk x, hxbar_mem⟩ :
            ↥((L ⊓ (Subgroup.thompsonJ (S : Subgroup ↥H) p).map H.subtype).map mk)) ^ p ^ k = 1 :=
                hk
        have := congrArg (Subtype.val) hk'
        simpa using this
      -- order of `mk x` divides `|L̄|` (since `mk x ∈ L̄`).
      have hord_dvd_Lbar : orderOf (mk x) ∣ Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
        Subgroup.orderOf_dvd_natCard _ hxbar_Lbar
      -- `|L̄|` is a `p'`-number, so coprime to `p^k`; hence `orderOf (mk x) = 1`.
      have hp_not_dvd_Lbar : ¬ p ∣ Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
        intro hdvd
        exact (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore
          ({p} : Set ℕ) G) {q | q ≠ p} p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
      have hcop : Nat.Coprime (p ^ k) (Nat.card (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
        Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_Lbar)
      have hord_one : orderOf (mk x) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hord_dvd_pk hord_dvd_Lbar
      exact orderOf_eq_one_iff.mp hord_one
    -- `mk x = 1 ⇒ x ∈ ker mk = U`.
    have hx_U : x ∈ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
      (QuotientGroup.eq_one_iff x).mp hxbar_one
    rwa [← hU_eq_oPi] at hx_U
  exact (hgoal_map.trans hinf_map_le).trans hLinf_le_U

end OddOrder.Isaacs.Ch07
