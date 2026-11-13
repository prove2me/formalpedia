-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.step4_5_normal_J_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:00:04.10023+00:00
-- url     : https://prove2.me/submissions/32946e6e-009e-42ed-8180-d6621e5ade81

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
import Theorems.Thm_OddOrder_Isaacs_Ch07_AbarInf_LBar_eq_bot
import Theorems.Thm_OddOrder_Isaacs_Ch07_step3_Abar_centralizes_inter_LBar
import Theorems.Thm_OddOrder_Isaacs_Ch07_step5_Abar_card_eq_p

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

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- For `N ⊴ G` and `A` with `N ⊓ A = ⊥`, the relative index `A.relIndex (N ⊔ A)`
equals `Nat.card N`.  (Diamond isomorphism: `|NA : A| = |N : N ⊓ A| = |N|`.) -/
private theorem relIndex_sup_of_inf_eq_bot
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G} [N.Normal]
    (h_inf : N ⊓ A = ⊥) :
    A.relIndex (N ⊔ A) = Nat.card N := by
  classical
  -- `|NA| = |A| * (A.relIndex NA)` (card_mul_index inside `↥(N ⊔ A)`).
  have hA_le : A ≤ N ⊔ A := le_sup_right
  have hN_le : N ≤ N ⊔ A := le_sup_left
  have h1 : Nat.card (A.subgroupOf (N ⊔ A)) * (A.subgroupOf (N ⊔ A)).index =
      Nat.card ↥(N ⊔ A) := Subgroup.card_mul_index _
  have h1' : Nat.card A * A.relIndex (N ⊔ A) = Nat.card ↥(N ⊔ A) := by
    rw [← h1]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv).symm
  -- `|NA| = |N| * (N.relIndex NA)` and `N.relIndex NA = N.relIndex A = |A|`.
  have h2 : Nat.card (N.subgroupOf (N ⊔ A)) * (N.subgroupOf (N ⊔ A)).index =
      Nat.card ↥(N ⊔ A) := Subgroup.card_mul_index _
  have hNrel : (N.subgroupOf (N ⊔ A)).index = Nat.card A := by
    change N.relIndex (N ⊔ A) = Nat.card A
    rw [Subgroup.relIndex_sup_left]
    -- `N.relIndex A = |A : N ⊓ A| = |A : ⊥| = |A|`.
    change (N.subgroupOf A).index = Nat.card A
    have : N.subgroupOf A = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot]
      rw [disjoint_iff]; exact h_inf
    rw [this, Subgroup.index_bot]
  have h2' : Nat.card N * Nat.card A = Nat.card ↥(N ⊔ A) := by
    rw [← h2, hNrel]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv).symm
  -- Cancel `Nat.card A` from `|A| * relIndex = |N| * |A|`.
  have hA_pos : 0 < Nat.card A := Nat.card_pos
  have hfin : Nat.card A * A.relIndex (N ⊔ A) = Nat.card A * Nat.card N := by
    rw [h1', ← h2', mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hA_pos hfin

/-- **Isaacs Thm 7.6 Steps 4 + 5** (mmd L3870-3878).

Together Steps 4-5 produce `P = UA ∧ A.relIndex U = p` given:
* The full Thm 7.6 hypotheses (i)-(v) on the running `G`.
* An induction hypothesis: Thm 7.6 holds for all proper subgroups `H < G`.
* A chosen `A ∈ E(P)` with `A ⊄ U` (Step 2 extraction).

**Step 4** (`P = UA`) is proved here as actual theorem code, using the focused
Step 3 lemma (`step3_Abar_centralizes_inter_LBar`).  **Step 5** (`|Ā| = p`)
is delegated to the focused `step5_Abar_card_eq_p` lemma.

Step 3 is **internal to this lemma**: both Step 4 and Step 5 use Step 3 by
applying the IH to proper subgroups (`H = LA` for Step 4, `H = MA` for any
Ā-invariant proper `M̄ < L̄` for Step 5).

The "|A : A ⊓ U|" formulation (= `A.relIndex U`) is used because the landed
Step 7 lemma (`omega1ZCenterOpCore_relIndex_inter_A_le`) consumes it directly. -/
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
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G) ∧
      (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set L : Subgroup G := opPpPrimeCore G p with hL_def
  set mk : G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) with hmk_def
  -- `U = O_{{p}}(G)` (kernel of `mk`), and `U ≤ L`.
  have hU_eq_oPi : U = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hker_mk : mk.ker = U := by rw [hmk_def, QuotientGroup.ker_mk', hU_eq_oPi]
  have hU_le_L : U ≤ L := by
    rw [hU_eq_oPi, hL_def]; exact oPiCore_p_le_opPpPrimeCore
  -- Basic facts about `A` and `U`.
  have hA_le_P : A ≤ (P : Subgroup G) := hA_mem.1
  have hA_pg : IsPGroup p A := hA_mem.2.1.isPGroup
  have hU_le_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  -- `UA = U ⊔ A`, `LA = L ⊔ A`.
  set UA : Subgroup G := U ⊔ A with hUA_def
  set LA : Subgroup G := L ⊔ A with hLA_def
  have hUA_le_P : UA ≤ (P : Subgroup G) := sup_le hU_le_P hA_le_P
  have hUA_le_LA : UA ≤ LA := sup_le_sup_right hU_le_L A
  have hUA_pg : IsPGroup p ↥UA :=
    P.isPGroup'.of_injective (Subgroup.inclusion hUA_le_P)
      (Subgroup.inclusion_injective hUA_le_P)
  -- `Ā = A.map mk`, `L̄ = L.map mk = O_{p'}(Ḡ)`.
  set Abar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := A.map mk
    with hAbar_def
  set Lbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := L.map mk
    with hLbar_def
  have hLbar_eq : Lbar = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
    rw [hLbar_def, hL_def, hmk_def]; exact opPpPrimeCore_map_eq_LBar
  have : Lbar.Normal := by rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.normal _ _
  -- `Ā ⊓ L̄ = ⊥` (p-group vs p'-group) and `Ā ≠ ⊥`.
  have hAbar_inf_Lbar : Abar ⊓ Lbar = ⊥ := by
    rw [hAbar_def, hLbar_eq]; exact AbarInf_LBar_eq_bot hA_pg
  have hAbar_ne_bot : Abar ≠ ⊥ := by
    rw [hAbar_def, hmk_def]
    exact Abar_ne_bot_of_not_le (by rwa [hU_eq_oPi] at hA_not_le)
  -- Step 4: prove `LA = ⊤`, then `UA = P`.
  have hLA_top : LA = ⊤ := by
    by_contra hLA_ne_top
    -- Build the Sylow `p`-subgroup `UA.subgroupOf LA` of `↥LA`.
    have hUA_le_LA' : UA ≤ LA := hUA_le_LA
    have hL_le_LA : L ≤ LA := le_sup_left
    have hA_le_LA : A ≤ LA := le_sup_right
    -- `UA.subgroupOf LA` is a `p`-group.
    have hUAsub_pg : IsPGroup p ↥(UA.subgroupOf LA) := hUA_pg.comap_subtype
    -- Its index in `↥LA` is `UA.relIndex LA = Nat.card L̄`, a `p'`-number.
    have hidx_eq : (UA.subgroupOf LA).index = UA.relIndex LA := rfl
    -- `UA.relIndex LA = Nat.card Lbar` via `relIndex_map_map` + diamond.
    have hrelindex_map : (Abar).relIndex (Lbar ⊔ Abar) = UA.relIndex LA := by
      rw [hAbar_def, hLbar_def]
      rw [← Subgroup.map_sup]
      rw [Subgroup.relIndex_map_map mk A (L ⊔ A)]
      rw [hker_mk]
      -- `(A ⊔ U).relIndex ((L ⊔ A) ⊔ U) = UA.relIndex LA` since `U ≤ A⊔U`, `U ≤ LA`.
      congr 1
      · rw [hUA_def, sup_comm]
      · rw [hLA_def]; rw [sup_assoc, sup_comm A U, ← sup_assoc, sup_eq_left.mpr hU_le_L]
    have hAbar_relindex : (Abar).relIndex (Lbar ⊔ Abar) = Nat.card Lbar :=
      relIndex_sup_of_inf_eq_bot (by rw [inf_comm]; exact hAbar_inf_Lbar)
    have hUA_relindex_LA : UA.relIndex LA = Nat.card Lbar := by
      rw [← hrelindex_map, hAbar_relindex]
    -- `Nat.card Lbar` is a `p'`-number, so `p ∤ (UA.subgroupOf LA).index`.
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸
          OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    have hp_not_dvd : ¬ p ∣ (UA.subgroupOf LA).index := by
      rw [hidx_eq, hUA_relindex_LA]
      intro hdvd
      exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
    -- The Sylow subgroup `S`.
    let S : Sylow p ↥LA := hUAsub_pg.toSylow hp_not_dvd
    have hS_coe : (S : Subgroup ↥LA) = UA.subgroupOf LA := hUAsub_pg.toSylow_coe hp_not_dvd
    -- `S = (LA ⊓ P).subgroupOf LA`: both are `p`-subgroups, `S` Sylow, `S ≤ (LA⊓P)sub`.
    have hLAP_pg : IsPGroup p ↥((LA ⊓ (P : Subgroup G)).subgroupOf LA) := by
      have : IsPGroup p ↥(LA ⊓ (P : Subgroup G)) :=
        P.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hS_le_LAP : (S : Subgroup ↥LA) ≤ (LA ⊓ (P : Subgroup G)).subgroupOf LA := by
      rw [hS_coe]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨x.property, hUA_le_P hx⟩
    have hS_eq_LAP : ((LA ⊓ (P : Subgroup G)).subgroupOf LA) = (S : Subgroup ↥LA) :=
      S.is_maximal' hLAP_pg hS_le_LAP
    -- Apply Step 3 with `H = LA`: `⁅L ⊓ LA, A⁆ ≤ U`.
    have hUA_le_H : U ⊔ A ≤ LA := sup_le (hU_le_L.trans hL_le_LA) hA_le_LA
    have hStep3 : (⁅L ⊓ LA, A⁆ : Subgroup G) ≤ U :=
      step3_Abar_centralizes_inter_LBar P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
        h_centralizer_center ih hA_mem hLA_ne_top hUA_le_H S hS_eq_LAP.symm
    -- `L ⊓ LA = L` (since `L ≤ LA`).
    have hL_inf_LA : L ⊓ LA = L := inf_eq_left.mpr hL_le_LA
    rw [hL_inf_LA] at hStep3
    -- `⁅L, A⁆ ≤ U = ker mk` ⇒ `⁅L̄, Ā⁆ = ⊥` ⇒ `Ā ≤ C_Ḡ(L̄)`.
    have hcomm_map : (⁅L, A⁆ : Subgroup G).map mk = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hker_mk]; exact hStep3
    have hAbar_le_cent : Abar ≤ Subgroup.centralizer (Lbar : Set _) := by
      rw [hAbar_def, hLbar_def, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
        ← Subgroup.map_commutator]
      rw [Subgroup.commutator_comm]
      exact hcomm_map
    -- Step 1(c): `C_Ḡ(L̄) ≤ L̄`.
    have hcent_le_Lbar : Subgroup.centralizer (Lbar : Set _) ≤ Lbar := by
      rw [hLbar_eq]; exact step1_c_centralizer_oPiPrime_quotient_le_self
    -- So `Ā ≤ L̄`, hence `Ā = Ā ⊓ L̄ = ⊥`, contradiction.
    have hAbar_le_Lbar : Abar ≤ Lbar := hAbar_le_cent.trans hcent_le_Lbar
    have hAbar_bot : Abar = ⊥ := by
      rw [← inf_eq_left.mpr hAbar_le_Lbar]; exact hAbar_inf_Lbar
    exact hAbar_ne_bot hAbar_bot
  -- From `LA = ⊤`: `UA = LA ⊓ P = ⊤ ⊓ P = P`.  Use `UA = LA ⊓ P`.
  have hUA_eq_P : UA = (P : Subgroup G) := by
    -- We re-derive the Sylow identity at `H = LA = ⊤`: `UA.subgroupOf LA = (LA⊓P).subgroupOf LA`,
    -- then map back.  With `LA = ⊤`, `LA ⊓ P = P`.
    apply le_antisymm hUA_le_P
    -- `P ≤ UA`: since `LA = ⊤`, `P ≤ LA`, and `LA ⊓ P = P` is a `p`-subgroup of `↥LA`
    -- containing the Sylow `UA.subgroupOf LA`, forcing equality.
    have hP_le_LA : (P : Subgroup G) ≤ LA := by rw [hLA_top]; exact le_top
    have hUAsub_pg : IsPGroup p ↥(UA.subgroupOf LA) := hUA_pg.comap_subtype
    have hidx_eq : (UA.subgroupOf LA).index = UA.relIndex LA := rfl
    have hrelindex_map : (Abar).relIndex (Lbar ⊔ Abar) = UA.relIndex LA := by
      rw [hAbar_def, hLbar_def, ← Subgroup.map_sup, Subgroup.relIndex_map_map mk A (L ⊔ A),
        hker_mk]
      congr 1
      · rw [hUA_def, sup_comm]
      · rw [hLA_def, sup_assoc, sup_comm A U, ← sup_assoc, sup_eq_left.mpr hU_le_L]
    have hAbar_relindex : (Abar).relIndex (Lbar ⊔ Abar) = Nat.card Lbar :=
      relIndex_sup_of_inf_eq_bot (by rw [inf_comm]; exact hAbar_inf_Lbar)
    have hLbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ≠ p} Lbar := by
      rw [hLbar_eq]; exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G ⧸
          OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) {q | q ≠ p}
    have hp_not_dvd : ¬ p ∣ (UA.subgroupOf LA).index := by
      rw [hidx_eq, hrelindex_map.symm.trans hAbar_relindex]
      intro hdvd
      exact (hLbar_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) rfl
    let S : Sylow p ↥LA := hUAsub_pg.toSylow hp_not_dvd
    have hS_coe : (S : Subgroup ↥LA) = UA.subgroupOf LA := hUAsub_pg.toSylow_coe hp_not_dvd
    have hLAP_pg : IsPGroup p ↥((LA ⊓ (P : Subgroup G)).subgroupOf LA) := by
      have : IsPGroup p ↥(LA ⊓ (P : Subgroup G)) :=
        P.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hS_le_LAP : (S : Subgroup ↥LA) ≤ (LA ⊓ (P : Subgroup G)).subgroupOf LA := by
      rw [hS_coe]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨x.property, hUA_le_P hx⟩
    have hS_eq_LAP : ((LA ⊓ (P : Subgroup G)).subgroupOf LA) = (S : Subgroup ↥LA) :=
      S.is_maximal' hLAP_pg hS_le_LAP
    -- So `(LA⊓P).subgroupOf LA = UA.subgroupOf LA`, hence `LA ⊓ P = UA` (both ≤ LA).
    rw [hS_coe] at hS_eq_LAP
    have hLAP_eq_UA : LA ⊓ (P : Subgroup G) = UA := by
      have hmap := congrArg (fun K : Subgroup ↥LA => K.map LA.subtype) hS_eq_LAP
      simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, LA.range_subtype] at hmap
      rwa [inf_eq_right.mpr (inf_le_left), inf_eq_right.mpr hUA_le_LA] at hmap
    -- `P ≤ LA ⊓ P = UA`.
    intro x hxP
    rw [← hLAP_eq_UA]
    exact ⟨hP_le_LA hxP, hxP⟩
  refine ⟨hUA_eq_P, ?_⟩
  -- Step 5 (delegated): `U.relIndex A = p`.
  exact step5_Abar_card_eq_p P hp2 h_pSolvable h2abelian h_oPiPrime_trivial
    h_centralizer_center ih hA_mem hA_not_le hUA_eq_P

end OddOrder.Isaacs.Ch07
