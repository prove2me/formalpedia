-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.step8a_PBar_normal_GBar
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:54:03.211273+00:00
-- url     : https://prove2.me/submissions/d6fc1acb-be06-4f78-9378-18d1b29900d2

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Theorems.Thm_OddOrder_Isaacs_Ch07_quotient_two_subgroup_abelian
import Theorems.Thm_OddOrder_Isaacs_Ch07_sylow_normal_of_elementary_normal_P_theorem

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- If `Q = P^g`, then `C_V(Q) = C_V(P)^g` for the action `φ`.

This is the Lean form of the first conjugacy step in Isaacs Thm 7.5. -/
theorem actionCentralizer_map_conj {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) (g : A) :
    actionCentralizer φ (P.map (MulAut.conj g).toMonoidHom) =
      (φ g : MulAut V) • actionCentralizer φ P := by
  ext v
  constructor
  · intro hv
    refine ⟨(φ g)⁻¹ v, ?_, MulAut.apply_inv_self V (φ g) v⟩
    intro p
    have hfix := hv ⟨(MulAut.conj g) p,
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom p.property⟩
    change (φ ((MulAut.conj g) (p : A))) v = v at hfix
    have hfix'' : (φ (g * (p : A) * g⁻¹)) v = v := by
      simpa [MulAut.conj_apply] using hfix
    have h := congrArg (fun x : V => (φ g)⁻¹ x) hfix''
    simpa [map_mul] using h
  · rintro ⟨u, hu, rfl⟩ q
    rcases q.property with ⟨p, hp, hq⟩
    have hpfix := hu ⟨p, hp⟩
    have h := congrArg (fun x : V => (φ g) x) hpfix
    have hq' : q.val = g * p * g⁻¹ := by
      simpa [MulAut.conj_apply] using hq.symm
    change (φ q.val) ((φ g) u) = (φ g) u
    rw [hq']
    simpa [map_mul] using h

/-- Conjugate subgroups have action-centralizers of the same index. -/
theorem actionCentralizer_map_conj_index {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) (g : A) :
    (actionCentralizer φ (P.map (MulAut.conj g).toMonoidHom)).index =
      (actionCentralizer φ P).index := by
  rw [actionCentralizer_map_conj]
  have h := Subgroup.relIndex_pointwise_smul (h := (φ g : MulAut V))
    (J := actionCentralizer φ P) (K := (⊤ : Subgroup V))
  have htop : (φ g : MulAut V) • (⊤ : Subgroup V) = ⊤ := by
    rw [Subgroup.pointwise_smul_def]
    exact Subgroup.map_top_of_surjective _ (fun v => ⟨(φ g)⁻¹ v, by simp⟩)
  simpa [htop] using h

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem zCenterOpCoreSubgroup_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    zCenterOpCoreSubgroup G p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  rintro _ ⟨⟨z, hz_L⟩, _, rfl⟩
  exact hz_L

/-- `V ≤ O_p(G)`: immediate via the chain `V ≤ Z(O_p(G)) ≤ O_p(G)`. -/
theorem omega1ZCenterOpCore_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
  omega1ZCenterOpCore_le_zCenterOpCore.trans zCenterOpCoreSubgroup_le_opCore

/-- `V := Ω₁(Z(O_p(G)))` is a `p`-group.

Direct consequence of `V ≤ O_p(G)` and `O_p(G)` being a `p`-group. -/
theorem omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (omega1ZCenterOpCore G p) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).of_injective
    (Subgroup.inclusion omega1ZCenterOpCore_le_opCore)
    (Subgroup.inclusion_injective _)

/-- `V ⊆ centralizer U` in `G`: since `V ⊆ Z(U)`, every element of `V`
commutes with every element of `U`.  Used in Step 7 to argue `V * D`
is abelian (`V ⊆ centralizer U ⊇ D`). -/
theorem omega1ZCenterOpCore_centralizes_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  intro x hx
  have hx_ZU : x ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore hx
  rcases hx_ZU with ⟨⟨z, hz_U⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm : (⟨u, hu⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) * ⟨z, hz_U⟩ =
      ⟨z, hz_U⟩ * ⟨u, hu⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  exact congr_arg Subtype.val hcomm

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `O_p(G) ≤ ker (MulAut.conjNormal : G →* MulAut V)`: every `u ∈ U`
centralizes `V = Ω₁ Z(U)` (since `V ⊆ Z(U)`). -/
private theorem opCore_le_ker_conjNormal_omega1ZCenterOpCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p G ≤
      (MulAut.conjNormal (H := omega1ZCenterOpCore G p)).ker := by
  intro u hu_U
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  -- Goal: (MulAut.conjNormal u) v = (1 : MulAut V) v = v
  apply Subtype.ext
  -- Goal: ↑((MulAut.conjNormal u) v) = ↑v
  rw [MulAut.conjNormal_apply]
  -- Goal: u * v * u⁻¹ = v
  have hv_cent : (v : G) ∈ Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore v.property
  have hvu : (u : G) * (v : G) = (v : G) * (u : G) :=
    (Subgroup.mem_centralizer_iff.mp hv_cent) u hu_U
  -- Convert "(1 : MulAut V) v" on the RHS.
  change (u : G) * (v : G) * (u : G)⁻¹ = (v : G)
  calc (u : G) * (v : G) * (u : G)⁻¹
      = (v : G) * (u : G) * (u : G)⁻¹ := by rw [hvu]
    _ = (v : G) := by group

/-- **The factored action `Ḡ →* MulAut V`**: lifts `MulAut.conjNormal` via
`U ≤ ker`. -/
private noncomputable def conjActionOnOmega1ZCenter_quotient
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) →*
      MulAut ↥(omega1ZCenterOpCore G p) :=
  QuotientGroup.lift _ MulAut.conjNormal (by
    rw [show OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G =
        OddOrder.Isaacs.Ch01.opCore p G from
      OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p]
    exact opCore_le_ker_conjNormal_omega1ZCenterOpCore)

/-- The kernel of `MulAut.conjNormal : G →* MulAut V` (for a normal subgroup `V`)
is exactly `C_G(V)`: `g` acts trivially on `V` iff `g` centralizes `V`. -/
private theorem conjNormal_ker_eq_centralizer
    {G : Type*} [Group G] {V : Subgroup G} [V.Normal] :
    (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg v hv
    -- `conjNormal g = 1` ⇒ `g * v * g⁻¹ = v`, i.e. `g * v = v * g`.
    have hfix : (MulAut.conjNormal g (⟨v, hv⟩ : V) : G) = ((⟨v, hv⟩ : V) : G) := by
      rw [hg]; rfl
    rw [MulAut.conjNormal_apply] at hfix
    -- `g * v * g⁻¹ = v` ⇒ `g * v = v * g`.
    have : g * v * g⁻¹ * g = v * g := by rw [hfix]
    have hcomm : g * v = v * g := by simpa [mul_assoc] using this
    exact hcomm.symm
  · intro hg
    -- Every `v ∈ V` is fixed: `g * v * g⁻¹ = v`.
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    simp only [MulAut.one_apply]
    rw [MulAut.conjNormal_apply]
    have hcomm : (v : G) * g = g * (v : G) := hg (v : G) v.property
    -- `g * v * g⁻¹ = v * g * g⁻¹ = v`.
    rw [← hcomm]; group

/-- **Isaacs Thm 7.6 Step 8a** (mmd L3893-3895): apply Thm 7.5.

Given Step 4-5-6-7 outputs:
* `P = UA` (Step 4)
* `|Ā| = p` (Step 5)
* The Ḡ-action on V is faithful (= Step 6, landed via
  `centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore`)
* `|V : V ∩ A| ≤ p` (Step 7, landed via `omega1ZCenterOpCore_relIndex_inter_A_le`)
plus the running Thm 7.6 hypotheses (i)-(v),

apply Thm 7.5 (`sylow_normal_of_elementary_normal_P_theorem`) to derive
`P̄ ⊴ Ḡ`. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp2 : p ≠ 2)
    (_h_pSolvable : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (_h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (_h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {A : Subgroup G}
    (hA_mem : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (h_P_eq_UA : OddOrder.Isaacs.Ch01.opCore p G ⊔ A = (P : Subgroup G))
    (_h_Abar_card_eq_p :
       (OddOrder.Isaacs.Ch01.opCore p G).relIndex A = p)
    (h_V_inter_A_le_p : A.relIndex (omega1ZCenterOpCore G p) ≤ p)
    (h_K_map_eq_bot :
       (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
         (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥) :
    ((P : Subgroup G).map
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))).Normal := by
  classical
  -- Abbreviations: `U = O_p(G) = O_{{p}}(G)`, `Ḡ = G/U`, `V = Ω₁(Z(U))`,
  -- `φ : Ḡ →* MulAut V` the lifted conjugation action.
  set U : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G with hU_def
  set mk : G →* G ⧸ U := QuotientGroup.mk' U with hmk_def
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set φ : (G ⧸ U) →* MulAut ↥V := conjActionOnOmega1ZCenter_quotient G p with hφ_def
  -- `U = O_p(G)` definitionally.
  have hU_eq : U = OddOrder.Isaacs.Ch01.opCore p G :=
    OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p
  -- (Hypothesis 1) `Ḡ` is `p`-separable: instance from `quotient_isPiSeparable`.
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (G ⧸ U) := inferInstance
  -- (Hypothesis 3) Every `2`-subgroup of `Ḡ` is abelian, by `quotient_two_subgroup_abelian`.
  have h2abelian_bar :
      ∀ S : Subgroup (G ⧸ U), IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x :=
    fun S hS2 => quotient_two_subgroup_abelian h2abelian S hS2
  -- (Hypothesis 4) `φ` is faithful: `ker φ = C_G(V).map mk = ⊥`.
  have hφ_inj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    -- `ker φ = (conjNormal).ker.map mk = C_G(V).map mk`.
    have hker : φ.ker = (Subgroup.centralizer (V : Set G)).map mk := by
      rw [hφ_def, hmk_def]
      unfold conjActionOnOmega1ZCenter_quotient
      rw [QuotientGroup.ker_lift, conjNormal_ker_eq_centralizer]
    rw [hker]
    exact h_K_map_eq_bot
  -- (Hypothesis 5 ingredient) `V` is a `p`-group.
  have hV_pg : IsPGroup p ↥V := omega1ZCenterOpCore_isPGroup p
  -- The candidate normal Sylow `P̄ = P.map mk` as a `Sylow p Ḡ`.
  set PBar : Sylow p (G ⧸ U) := P.mapSurjective (QuotientGroup.mk'_surjective U) with hPBar_def
  have hPBar_coe : (PBar : Subgroup (G ⧸ U)) = (P : Subgroup G).map mk := by
    rw [hPBar_def, Sylow.coe_mapSurjective]
  -- `P̄ = Ā` since `Ū = ⊥` and `P = UA`.
  have hPBar_eq_Abar : (PBar : Subgroup (G ⧸ U)) = A.map mk := by
    rw [hPBar_coe, ← h_P_eq_UA, ← hU_eq, Subgroup.map_sup]
    -- `U.map mk = ⊥`.
    have hU_map : U.map mk = ⊥ := by
      rw [hmk_def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hU_map, bot_sup_eq]
  -- `A` is abelian (it is elementary abelian).
  have hA_comm : ∀ a b : ↥A, a * b = b * a := (hA_mem.2.1).comm
  -- Key step: `(actionCentralizer φ P̄).index ≤ p`, because `E = V ∩ A` is fixed by `P̄ = Ā`.
  -- Membership: every `v : ↥V` whose underlying element lies in `A` is `P̄`-fixed.
  have hE_le_centralizer :
      (A.subgroupOf V) ≤ actionCentralizer φ (PBar : Subgroup (G ⧸ U)) := by
    intro v hv
    -- `hv : (v : G) ∈ A` (membership of the subgroupOf).
    rw [Subgroup.mem_subgroupOf] at hv
    rw [mem_actionCentralizer]
    intro q
    -- `q ∈ P̄ = Ā`, so `q = mk a` for some `a ∈ A`.
    have hq_mem : (q : G ⧸ U) ∈ A.map mk := hPBar_eq_Abar ▸ q.property
    obtain ⟨a, ha_A, ha_eq⟩ := hq_mem
    -- `φ q v = φ (mk a) v = conjNormal a v = a * v * a⁻¹ = v` (A abelian).
    apply Subtype.ext
    have hφq : φ (q : G ⧸ U) = MulAut.conjNormal a := by
      rw [hφ_def]
      unfold conjActionOnOmega1ZCenter_quotient
      rw [← ha_eq, hmk_def]
      exact QuotientGroup.lift_mk' _ _ a
    rw [hφq, MulAut.conjNormal_apply]
    -- `a * v * a⁻¹ = v` since `a, v ∈ A` and `A` is abelian.
    have hcomm : a * (v : G) = (v : G) * a :=
      congrArg Subtype.val (hA_comm ⟨a, ha_A⟩ ⟨(v : G), hv⟩)
    rw [hcomm]; group
  -- `(actionCentralizer φ P̄).index ≤ (A.subgroupOf V).index = A.relIndex V ≤ p`.
  have hPBar_index : (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index ≤ p := by
    have h1 : (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index ≤
        (A.subgroupOf V).index := Subgroup.index_antitone hE_le_centralizer
    calc (actionCentralizer φ (PBar : Subgroup (G ⧸ U))).index
        ≤ (A.subgroupOf V).index := h1
      _ = A.relIndex V := rfl
      _ ≤ p := h_V_inter_A_le_p
  -- Extend the bound to *every* Sylow of `Ḡ` via conjugacy.
  have h_centralizer_index :
      ∀ R : Sylow p (G ⧸ U), (actionCentralizer φ (R : Subgroup (G ⧸ U))).index ≤ p := by
    intro R
    -- `R` and `P̄` are conjugate: `R = ḡ • P̄`.
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ U) PBar R
    have hR_eq : (R : Subgroup (G ⧸ U)) =
        (PBar : Subgroup (G ⧸ U)).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hR_eq, actionCentralizer_map_conj_index]
    exact hPBar_index
  -- Apply Theorem 7.5 to `φ : Ḡ →* MulAut V` and the Sylow `P̄`.
  have hPBar_normal : (PBar : Subgroup (G ⧸ U)).Normal :=
    sylow_normal_of_elementary_normal_P_theorem hp2 h2abelian_bar hφ_inj hV_pg
      h_centralizer_index PBar
  -- Transport normality to `(P : Subgroup G).map mk`.
  rwa [hPBar_coe] at hPBar_normal

end OddOrder.Isaacs.Ch07
