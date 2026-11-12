-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.step5_Abar_card_eq_p
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:55:58.914198+00:00
-- url     : https://prove2.me/submissions/e4d4fc70-22c0-4710-ba0a-bdcf387768de

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Basic
import Definitions.Def_OddOrder_GroupTheory_OpResidual
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Theorem315
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Theorems.Thm_OddOrder_Isaacs_Ch06_isCyclic_of_faithful_trivial_on_proper_invariant
import Theorems.Thm_OddOrder_Isaacs_Ch07_AbarInf_LBar_eq_bot
import Theorems.Thm_OddOrder_Isaacs_Ch07_step3_Abar_centralizes_inter_LBar

-- ===== OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean =====
namespace OddOrder.Isaacs.Ch03

open SemidirectProduct

open scoped Pointwise

section

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- The π-Fitting series is contained in the complementary π-Fitting series.

The successor step maps the quotient by `F_n(π)` onto the quotient by `F_n(π')`;
`O_π` and `O_{π'}` are then carried into the two summands on the complementary side. -/
theorem piFittingSeries_le_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G] :
    ∀ n, piFittingSeries π G n ≤ piFittingSeries {p | p ∉ π} G n := by
  intro n
  induction n with
  | zero =>
      rw [piFittingSeries_zero, piFittingSeries_zero]
  | succ n ih =>
      intro x hx
      set π' : Set ℕ := {p | p ∉ π} with hπ'_def
      set F : Subgroup G := piFittingSeries π G n with hF_def
      set F' : Subgroup G := piFittingSeries π' G n with hF'_def
      have hF_le_F' : F ≤ F' := by
        intro y hy
        exact ih hy
      set Q : G ⧸ F →* G ⧸ F' :=
        QuotientGroup.map F F' (MonoidHom.id G) hF_le_F' with hQ_def
      have hQsurj : Function.Surjective Q := by
        intro y
        rcases QuotientGroup.mk'_surjective F' y with ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk' F g, by simp [Q]⟩
      have hQ_eq : (QuotientGroup.mk' F') x = Q ((QuotientGroup.mk' F) x) := by
        simp [Q]
      rw [piFittingSeries_succ, Subgroup.mem_comap] at hx
      rw [piFittingSeries_succ, Subgroup.mem_comap]
      rw [show ({q | q ∉ π'} : Set ℕ) = π by
        ext q
        simp [π']]
      change (QuotientGroup.mk' F') x ∈
        oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F')
      rw [hQ_eq]
      have hxF : (QuotientGroup.mk' F) x ∈
          oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F) := by
        simpa [F, π', hπ'_def] using hx
      have hMapSup :
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q ≤
            oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
        calc
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q =
              (oPiCore π (G ⧸ F)).map Q ⊔ (oPiCore π' (G ⧸ F)).map Q := by
            rw [Subgroup.map_sup]
          _ ≤ oPiCore π (G ⧸ F') ⊔ oPiCore π' (G ⧸ F') :=
            sup_le_sup (oPiCore.map_le_of_surjective π Q hQsurj)
              (oPiCore.map_le_of_surjective π' Q hQsurj)
          _ = oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
            rw [sup_comm]
      exact hMapSup ⟨_, hxF, rfl⟩

/-- π-separability is symmetric under replacing `π` by its complement. -/
theorem isPiSeparable_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (hG : IsPiSeparable π G) : IsPiSeparable {p | p ∉ π} G := by
  rcases hG.exists_top with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hle := piFittingSeries_le_compl π G n
  rw [hn] at hle
  exact top_le_iff.mp hle

end

end OddOrder.Isaacs.Ch03

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 1(c)** (mmd L3839): in the quotient
`G̅ := G / O_p(G)`, the centralizer of `L̅ := O_{p'}(G̅)` is contained in `L̅`.

Stated with the quotient taken at `oPiCore ({p} : Set ℕ) G` (the canonical
form recognized by `oPiCore_quotient_self_eq_bot`).  Use sites that work with
`opCore p G` should transport across `oPiCore_singleton_eq_opCore` via
`QuotientGroup.quotientMulEquivOfEq` before calling. -/
theorem step1_c_centralizer_oPiPrime_quotient_le_self
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G] :
    Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
            (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
          Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
  -- (1) `{p}`-separability passes to the quotient (mathlib instance).
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := inferInstance
  -- (2) Take complement: `IsPiSeparable π G → IsPiSeparable {p | p ∉ π} G`.
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({q | q ≠ p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
    have hcompl := OddOrder.Isaacs.Ch03.isPiSeparable_compl
      ({p} : Set ℕ) (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) inferInstance
    have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
      ext q; simp
    rw [hπeq] at hcompl
    exact hcompl
  -- (3) Hall-Higman complement: `O_{{p}}(G̅) = ⊥` (self-quotient kills radical).
  have hπ'bot :
      OddOrder.Isaacs.Ch03.oPiCore
          ({q : ℕ | q ∉ ({q | q ≠ p} : Set ℕ)} : Set ℕ)
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by
    have hπ'eq : ({q : ℕ | q ∉ ({q | q ≠ p} : Set ℕ)} : Set ℕ) = ({p} : Set ℕ) := by
      ext q; simp
    rw [hπ'eq]
    exact OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)
  -- (4) Apply Hall-Higman 3.21 to `G̅` with `π = {q | q ≠ p}`.
  exact OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({q | q ≠ p} : Set ℕ) hπ'bot

/-- `U = O_p(G) ≤ L = O_{p',p}(G)`: the kernel of the quotient map lies in the
preimage of any subgroup of the quotient. -/
theorem oPiCore_p_le_opPpPrimeCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G ≤ opPpPrimeCore G p := by
  unfold opPpPrimeCore
  intro x hx
  rw [Subgroup.mem_comap]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
    (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).one_mem

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

/-- **Step 5 conclusion synthesizer** (mmd L3874): a nontrivial, finite,
elementary abelian, cyclic `p`-group has order exactly `p`.  Generic. -/
theorem card_eq_prime_of_isElementaryAbelian_isCyclic_nontrivial
    {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hH_el : OddOrder.GroupTheory.IsElementaryAbelian p H) (hH_cyc : IsCyclic H) :
    Nat.card H = p := by
  -- Get generator; |H| = orderOf g for cyclic.
  obtain ⟨g, hg⟩ := hH_cyc.exists_generator
  have hzgen : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => hg x⟩
  have hcard : Nat.card H = orderOf g := by
    have hcard_zpow : Nat.card (Subgroup.zpowers g) = Nat.card H := by
      rw [hzgen]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← hcard_zpow, Nat.card_zpowers]
  -- g^p = 1 ⇒ orderOf g ∣ p.
  have hpow : g ^ p = 1 := hH_el.pow_eq_one g
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hpow
  -- p prime + orderOf g ∣ p ⇒ orderOf g = 1 or p.
  rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp'
  · -- orderOf g = 1 ⇒ g = 1 ⇒ zpowers g = ⊥; but zpowers g = ⊤ (hzgen), contradict.
    exfalso
    have hg_eq : g = 1 := orderOf_eq_one_iff.mp h1
    have hbot : Subgroup.zpowers g = ⊥ := by
      rw [hg_eq, Subgroup.zpowers_one_eq_bot]
    have hcontra : (⊤ : Subgroup H) = ⊥ := hzgen.symm.trans hbot
    exact absurd hcontra top_ne_bot
  · rw [hcard, hp']

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

/-- **Isaacs Thm 7.6 Step 5 nontriviality** (mmd L3874): if `A ⊄ U`
(= `oPiCore {p} G`), then the image `Ā = A.map (mk' U)` is nontrivial.

Contrapositive: `Ā = ⊥ ⇒ A ≤ ker mk' = U`. -/
theorem Abar_ne_bot_of_not_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G}
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ≠ ⊥ := by
  intro h_eq
  apply hA_not_le
  intro x hx
  have hmem :
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) x ∈
        A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
    ⟨x, hx, rfl⟩
  rw [h_eq, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

/-- **Isaacs Thm 7.6 Step 5 faithfulness** (mmd L3874): for any `p`-subgroup
`A ≤ G`, the image `Ā = A.map (mk' U)` acts faithfully on `L̅ = O_{p'}(G̅)`,
i.e., `Ā ⊓ C_{G̅}(L̅) = ⊥`.

Combines Step 1(c) (`C_{G̅}(L̅) ⊆ L̅`) with `Ā ⊓ L̅ = ⊥`. -/
theorem AbarInf_centralizer_LBar_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
            (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
          Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [eq_bot_iff]
  calc
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
        Subgroup.centralizer
          (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
              (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
            Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
        ≤ A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
            OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
              (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
      inf_le_inf_left _ step1_c_centralizer_oPiPrime_quotient_le_self
    _ = ⊥ := AbarInf_LBar_eq_bot hA_pg

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Modular law, normalizer form** (mmd L3877): if `W ≤ L`, `A ⊓ L = ⊥`, and `A`
normalizes `W`, then `(W ⊔ A) ⊓ L = W`.  Used to show `W ⊔ Ā = ⊤ ⇒ W = L̄`.

The mathlib `IsModularLattice (Subgroup ·)` instance only covers `[CommGroup]`; here
the noncommutative case is handled by hand via the product representation `W·A` of
`W ⊔ A` (valid since `A ≤ N(W)`, so `W` is normal in `W ⊔ A`). -/
private theorem inf_sup_eq_of_le_normalizer_of_inf_eq_bot
    {G : Type*} [Group G] {W A L : Subgroup G}
    (hW_le : W ≤ L) (hA_inf : A ⊓ L = ⊥) (hAnorm : A ≤ Subgroup.normalizer (W : Set G)) :
    (W ⊔ A) ⊓ L = W := by
  apply le_antisymm
  · intro x ⟨hxWA, hxL⟩
    -- `W` is normal in `A ⊔ W`, so `x = w * a` with `w ∈ W`, `a ∈ A`.
    have : (W.subgroupOf (A ⊔ W)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAnorm
    have hx_AW : x ∈ A ⊔ W := by rw [sup_comm]; exact hxWA
    have hmem : (⟨x, hx_AW⟩ : ↥(A ⊔ W)) ∈ (W.subgroupOf (A ⊔ W)) ⊔ (A.subgroupOf (A ⊔ W)) := by
      rw [← Subgroup.subgroupOf_sup (le_sup_right) (le_sup_left), sup_comm W A,
        Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨⟨w, hw_AW⟩, hw, ⟨a, ha_AW⟩, ha, heq⟩ := hmem
    have hw_W : w ∈ W := hw
    have ha_A : a ∈ A := ha
    have hxeq : x = w * a := congrArg (Subtype.val) heq |>.symm
    -- `a = w⁻¹ * x ∈ L` (since `w ∈ W ≤ L`, `x ∈ L`), so `a ∈ A ⊓ L = ⊥`, `a = 1`.
    have ha_L : a ∈ L := by
      have : w⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hW_le hw_W)) hxL
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have ha_one : a = 1 := by
      have : a ∈ A ⊓ L := ⟨ha_A, ha_L⟩
      rw [hA_inf, Subgroup.mem_bot] at this; exact this
    rw [hxeq, ha_one, mul_one]; exact hw_W
  · exact le_inf le_sup_left hW_le

/-- **Isaacs Thm 7.6 Step 5, "trivial on proper invariant" clause** (mmd L3876-3878).

Given the running Thm 7.6 hypotheses, the IH, the chosen `A ∈ E(P)` with `A ⊄ U`,
and Step 4's output `P = UA`, every `Ā`-invariant proper subgroup `W < L̄` of
`L̄ = O_{p'}(Ḡ)` is centralized by `Ā` (`⁅W, Ā⁆ = ⊥`).

Book proof: set `M = preimage of W in G containing U` (`= W.comap mk`), so
`U ≤ M ≤ L`.  `A ≤ N_G(M)` (since `Ā` normalizes `W` and `U = ker mk ≤ M`),
hence `H = M ⊔ A` is proper (`H = ⊤` would force `W ⊔ Ā = ⊤`, and the modular
law `(W ⊔ Ā) ⊓ L̄ = W ⊔ (Ā ⊓ L̄) = W` would give `L̄ = W`, contradicting `W < L̄`)
with `P = UA ⊆ H` Sylow (`|H : P| = |W|`, a `p'`-number, via `relIndex`).  Step 3
applied to `H` gives `⁅L ⊓ H, A⁆ ≤ U`; since `M ≤ L ⊓ H`, `⁅M, A⁆ ≤ U = ker mk`,
so `⁅W, Ā⁆ = mk⁅M, A⁆ = ⊥`. -/
private theorem step5_Abar_centralizes_invariant_proper.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
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
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    {W : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)}
    (hW_le : W ≤ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
    (hW_ne : W ≠ OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
    (hW_normalized : ∀ a : G, a ∈ A → ∀ w, w ∈ W →
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) a * w *
        ((QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) a)⁻¹ ∈ W) :
    (⁅W, A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))⁆ :
      Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hLbar_def
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hker_mk : mk.ker = U := by rw [hmk_def, QuotientGroup.ker_mk', hU_eq_oPi]
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hU_le_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  -- `L = comap mk L̄`, and `L.map mk = L̄`.
  have hL_comap : L = Lbar.comap mk := by rw [hL_def, hLbar_def, hmk_def, opPpPrimeCore]
  have hLmap : L.map mk = Lbar := by rw [hL_def, hLbar_def, hmk_def]; exact
      opPpPrimeCore_map_eq_LBar
  have hU_le_L : U ≤ L := by rw [hU_eq_oPi, hL_def]; exact oPiCore_p_le_opPpPrimeCore
  -- `M = preimage of W`, `U ≤ M ≤ L`.
  set M : Subgroup G := W.comap mk with hM_def
  have hU_le_M : U ≤ M := by
    rw [hM_def, ← hker_mk]; intro x hx; rw [Subgroup.mem_comap, hx]; exact W.one_mem
  have hM_le_L : M ≤ L := by rw [hM_def, hL_comap]; exact Subgroup.comap_mono hW_le
  have hMmap : M.map mk = W := by
    rw [hM_def]; exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) W
  -- `H = M ⊔ A`.  `U ⊔ A ≤ H`, `P ≤ H`, `mk H = W ⊔ Abar`.
  set H : Subgroup G := M ⊔ A with hH_def
  have hUA_le_H : U ⊔ A ≤ H := sup_le_sup_right hU_le_M A
  have hP_le_H : (P : Subgroup G) ≤ H := by rw [← h_P_eq_UA]; exact hUA_le_H
  have hHmap : H.map mk = W ⊔ Abar := by
    rw [hH_def, Subgroup.map_sup, hMmap, hAbar_def]
  -- `Abar` normalizes `W` (from `hW_normalized`).
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_norm_W : Abar ≤ Subgroup.normalizer (W : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw; exact hW_normalized a ha w hw
    · intro hw
      have := hW_normalized a⁻¹ (A.inv_mem ha) _ hw
      simpa [map_inv, mul_assoc] using this
  -- `H ≠ ⊤`: else `W ⊔ Abar = ⊤`, modular law forces `W = L̄`.
  have hH_ne_top : H ≠ ⊤ := by
    intro hHtop
    apply hW_ne
    have hWAbar_top : W ⊔ Abar = ⊤ := by rw [← hHmap, hHtop, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    -- `(W ⊔ Abar) ⊓ L̄ = W` (modular law), and LHS `= ⊤ ⊓ L̄ = L̄`.
    have hmod := inf_sup_eq_of_le_normalizer_of_inf_eq_bot hW_le hAbar_inf_Lbar hAbar_norm_W
    rw [hWAbar_top, top_inf_eq] at hmod
    exact hmod.symm
  -- `P = UA ⊆ H` is a Sylow `p`-subgroup of `G` contained in `H`, hence Sylow in `↥H`
  -- (`Sylow.subtype`).  Since `P ⊆ H`, `H ⊓ P = P`, giving the form Step 3 wants.
  let S : Sylow p ↥H := P.subtype hP_le_H
  have hS_coe : (S : Subgroup ↥H) = (P : Subgroup G).subgroupOf H := P.coe_subtype hP_le_H
  have hHP_eq_P : H ⊓ (P : Subgroup G) = (P : Subgroup G) := inf_eq_right.mpr hP_le_H
  have hS_eq_HP : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H := by
    rw [hS_coe, hHP_eq_P]
  -- Step 3 applied to `H`: `⁅L ⊓ H, A⁆ ≤ U`.
  have hStep3 : (⁅L ⊓ H, A⁆ : Subgroup G) ≤ U :=
    step3_Abar_centralizes_inter_LBar P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
      h_centralizer_center ih hA_mem hH_ne_top hUA_le_H S hS_eq_HP
  -- `M ≤ L ⊓ H`, so `⁅M, A⁆ ≤ ⁅L ⊓ H, A⁆ ≤ U = ker mk`.
  have hM_le_LinfH : M ≤ L ⊓ H := le_inf hM_le_L le_sup_left
  have hMA_le_U : (⁅M, A⁆ : Subgroup G) ≤ U :=
    (Subgroup.commutator_mono hM_le_LinfH le_rfl).trans hStep3
  -- `⁅W, Abar⁆ = mk⁅M, A⁆ ≤ mk U = ⊥`.
  have hcomm_map : (⁅M, A⁆ : Subgroup G).map mk = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker_mk]; exact hMA_le_U
  rw [← hMmap, hAbar_def, ← Subgroup.map_commutator, hcomm_map]

/-- **Isaacs Thm 7.6 Step 5** (mmd L3874): `|Ā| = p`, equivalently
`(O_p(G)).relIndex A = p`.

Given Step 4's output `P = UA` plus the running hypotheses and the induction
hypothesis, `Ā = A.map mk'` acts faithfully and coprimely on `L̄ = O_{p'}(Ḡ)`
(faithful by Step 1(c) + `Ā ⊓ L̄ = ⊥`; coprime by `p` vs `p'`).  By Lemma 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`), `Ā` is cyclic — the
"trivial on every `Ā`-invariant proper subgroup `M̄ < L̄`" hypothesis is exactly
`step5_Abar_centralizes_invariant_proper` (Step 3 applied to `H = MA`).  A
nontrivial cyclic elementary abelian `p`-group has order `p`; the conversion of
`Nat.card Ā = p` to `(O_p(G)).relIndex A = p` is `relIndex_sup_of_inf_eq_bot`. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
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
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G)) :
    (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p := by
  classical
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G := h_pSolvable
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hLbar_def
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hLbar_normal : Lbar.Normal := by
    rw [hLbar_def]; exact OddOrder.Isaacs.Ch03.oPiCore.normal _ _
  -- `Ā ⊓ L̄ = ⊥`, `Ā ≠ ⊥`.
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_ne_bot : Abar ≠ ⊥ := by
    rw [hAbar_def, hmk_def]
    exact Abar_ne_bot_of_not_le (by rwa [hU_eq_oPi] at hA_not_le)
  -- The conjugation action `↥Ā ↷ ↥L̄`.  `a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`.
  let : MulDistribMulAction ↥Abar ↥Lbar := subgroupConjActionOnNormal Abar Lbar
  have hsmul_coe : ∀ (a : ↥Abar) (n : ↥Lbar),
      ((a • n : ↥Lbar) : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) =
        (↑a : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) * ↑n * (↑a)⁻¹ := by
    intro a n; rfl
  -- `Ā` is elementary abelian (image of the elementary abelian `A`).
  have hAbar_el : OddOrder.GroupTheory.IsElementaryAbelian p ↥Abar := by
    rw [hAbar_def]
    exact isElementaryAbelian_map_of_isElementaryAbelian mk
      (A := A) ⟨hA_mem.2.1.1, hA_mem.2.1.2⟩
  -- `↥Ā` is abelian.
  have : IsMulCommutative ↥Abar := ⟨⟨hAbar_el.1⟩⟩
  -- The action is faithful: `a` fixes all of `L̄` ⇒ `↑a ∈ C_Ḡ(L̄)`, and `Ā ⊓ C_Ḡ(L̄) = ⊥`.
  have hAbar_inf_cent :
      Abar ⊓ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
    rw [hAbar_def, hLbar_def]; exact AbarInf_centralizer_LBar_eq_bot hA_pg
  have : FaithfulSMul ↥Abar ↥Lbar := by
    refine ⟨fun {a b} h => ?_⟩
    -- `↑b⁻¹ * ↑a` centralizes `L̄`.
    set ga : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := a.1 with hga
    set gb : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := b.1 with hgb
    have hcent : gb⁻¹ * ga ∈ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have heq := h ⟨m, hm⟩
      rw [Subtype.ext_iff, hsmul_coe, hsmul_coe, ← hga, ← hgb] at heq
      -- `heq : ga * m * ga⁻¹ = gb * m * gb⁻¹`  ⇒  `m * (gb⁻¹ * ga) = (gb⁻¹ * ga) * m`.
      calc m * (gb⁻¹ * ga)
          = gb⁻¹ * (gb * m * gb⁻¹) * ga := by group
        _ = gb⁻¹ * (ga * m * ga⁻¹) * ga := by rw [heq]
        _ = (gb⁻¹ * ga) * m := by group
    have hmem : gb⁻¹ * ga ∈ Abar ⊓ Subgroup.centralizer
        (Lbar : Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
      ⟨Abar.mul_mem (Abar.inv_mem b.2) a.2, hcent⟩
    rw [hAbar_inf_cent, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem).symm
  -- Coprimality: `|Ā|` is a `p`-power, `|L̄|` is a `p'`-number.
  have hCop : Nat.Coprime (Nat.card ↥Abar) (Nat.card ↥Lbar) := by
    have hAbar_pg : IsPGroup p ↥Abar := by rw [hAbar_def]; exact hA_pg.map mk
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAbar_pg
    rw [hk]
    refine Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ?_)
    intro hdvd
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_def]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
        (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
  -- `hproper`: `Ā` acts trivially on every `Ā`-invariant proper `M̄ < L̄`.
  have hproper : ∀ M : Subgroup ↥Lbar, (∀ a : ↥Abar, ∀ n ∈ M, a • n ∈ M) → M ≠ ⊤ →
      ∀ a : ↥Abar, ∀ n ∈ M, a • n = n := by
    intro M hM_inv hM_ne_top a n hn
    -- Set `W = M.map L̄.subtype ≤ L̄`, proper, `Ā`-invariant; apply the focused lemma.
    set W : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := M.map Lbar.subtype
      with hW_def
    have hW_le : W ≤ Lbar := by rw [hW_def]; exact Subgroup.map_subtype_le M
    have hW_ne : W ≠ Lbar := by
      intro hWtop
      apply hM_ne_top
      apply Subgroup.map_injective Lbar.subtype_injective
      rw [← hW_def, hWtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hW_normalized : ∀ a : G, a ∈ A → ∀ w, w ∈ W → mk a * w * (mk a)⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨⟨w, hwL⟩, hwM, rfl⟩ := hw
      have hg_Abar : mk g ∈ Abar := Subgroup.mem_map_of_mem mk hg
      have hmoved := hM_inv ⟨mk g, hg_Abar⟩ ⟨w, hwL⟩ hwM
      rw [hW_def]
      have hsmul := hsmul_coe ⟨mk g, hg_Abar⟩ ⟨w, hwL⟩
      exact ⟨_, hmoved, hsmul⟩
    have hcomm := step5_Abar_centralizes_invariant_proper P hp2 h_pSolvable h2abelian
      h_oPiPrime_trivial h_centralizer_center ih hA_mem h_P_eq_UA hW_le hW_ne hW_normalized
    -- `⁅W, Ā⁆ = ⊥` ⇒ `Ā` centralizes `W` ⇒ `a • n = n`.
    apply Subtype.ext
    rw [hsmul_coe a n]
    -- `ga` and `gn` commute since `⁅W, Ā⁆ = ⊥` and `gn ∈ W`, `ga ∈ Ā`.
    set ga : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := a.1 with hga
    set gn : G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G := n.1 with hgn
    have hn_W : gn ∈ W := ⟨n, hn, rfl⟩
    have hcomm_mem : ⁅gn, ga⁆ ∈ (⊥ :
        Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hn_W a.2
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hcomm_mem
    -- `gn` and `ga` commute ⇒ `ga * gn * ga⁻¹ = gn`.
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm_mem.symm.eq
  -- Apply Lemma 6.20: `Ā` is cyclic.
  have hAbar_cyclic : IsCyclic ↥Abar :=
    OddOrder.Isaacs.Ch06.isCyclic_of_faithful_trivial_on_proper_invariant hCop hproper
  -- `Ā` is nontrivial, elementary abelian, cyclic `p`-group ⇒ `|Ā| = p`.
  have : Nontrivial ↥Abar := (Subgroup.nontrivial_iff_ne_bot _).mpr hAbar_ne_bot
  have hAbar_card : Nat.card ↥Abar = p :=
    card_eq_prime_of_isElementaryAbelian_isCyclic_nontrivial hAbar_el hAbar_cyclic
  -- Convert `Nat.card Ā = p` to `U.relIndex A = p` via `relIndex_map_map` + diamond.
  -- `U.relIndex A = |A : A ⊓ U| = |Ā| = p` (`Ā = A.map mk ≅ A / (A ⊓ U)`, `ker mk = U`).
  rw [← hAbar_card]
  -- `U.relIndex A = (U.subgroupOf A).index`; `U.subgroupOf A = ker (mk ∘ A.subtype)`.
  change (U.subgroupOf A).index = Nat.card ↥Abar
  have hker : U.subgroupOf A = (mk.comp A.subtype).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      hmk_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hU_eq_oPi]
  rw [hker]
  -- `|A : ker φ| = |range φ| = |A.map mk| = |Ā|` for `φ = mk ∘ A.subtype`.
  have hrange : (mk.comp A.subtype).range = Abar := by
    rw [hAbar_def, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact Subgroup.index_ker (mk.comp A.subtype)

end OddOrder.Isaacs.Ch07
