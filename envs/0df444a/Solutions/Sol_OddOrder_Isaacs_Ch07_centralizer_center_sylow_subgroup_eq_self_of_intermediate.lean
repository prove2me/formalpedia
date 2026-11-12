-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.centralizer_center_sylow_subgroup_eq_self_of_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:51:27.770278+00:00
-- url     : https://prove2.me/submissions/08e1a7a3-2112-439e-862b-d5dd56184852

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The image of `Z(P)` in `G` centralizes `O_p(G)`.

Pure structural fact: since `O_p(G) ≤ P`, any element of `Z(P)` commutes with
every element of `O_p(G)`.  Hypothesis (iv) `O_{p'}(G) = 1` is **not** needed
here; it enters only at the next step (Hall-Higman 3.21). -/
private theorem center_sylow_le_centralizer_opCore
    {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  rintro _ ⟨⟨z, hzP⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh_P : h ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P hh
  have hc : (⟨h, hh_P⟩ : (P : Subgroup G)) * ⟨z, hzP⟩
      = ⟨z, hzP⟩ * ⟨h, hh_P⟩ :=
    Subgroup.mem_center_iff.mp hz_center ⟨h, hh_P⟩
  exact congr_arg Subtype.val hc

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): Hall-Higman 3.21 with `π = {p}`.

If `G` is `{p}`-separable (equivalently `p`-solvable) and `O_{p'}(G) = ⊥`,
then `C_G(O_p(G)) ≤ O_p(G)`. -/
theorem centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  have hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ := by
    rw [show ({q | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} by
      ext q; simp]
    exact hOp'
  have hHH :=
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) ({p} : Set ℕ) hπ'
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p] at hHH
  exact hHH

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): `Z(P) ≤ O_p(G)` under `O_{p'}(G) = ⊥`.

Composition of `center_sylow_le_centralizer_opCore` (structural) and
`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot` (Hall-Higman 3.21).
This is the core conclusion of Step 1 in the 8-step proof of Thm 7.6. -/
theorem center_sylow_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  (center_sylow_le_centralizer_opCore P).trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot hOp')

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJClose.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 3 hypothesis (v)** (mmd L3852): for an intermediate
subgroup `U ≤ H ≤ G`, the Sylow `S = H ∩ P` of `↥H` satisfies `C_H(Z(S)) = S`.

Book proof: `Z(P) ⊆ U ⊆ S ⊆ P` gives `Z(P) ⊆ Z(S)`, so
`C_H(Z(S)) ⊆ C_G(Z(P)) = P` (hypothesis (v) on `G`), a `p`-subgroup of `H`
containing the Sylow `S`; maximality forces equality. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (h_oPiPrime_trivial : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {H : Subgroup G}
    (hU_le_H : OddOrder.Isaacs.Ch01.opCore p G ≤ H)
    (S : Sylow p ↥H)
    (hS_eq : (S : Subgroup ↥H) = (H ⊓ (P : Subgroup G)).subgroupOf H) :
    Subgroup.centralizer
        (((Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype) : Set ↥H)
      = (S : Subgroup ↥H) := by
  classical
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  -- `S` mapped to `G` is `H ⊓ P`.
  have hS_map : (S : Subgroup ↥H).map H.subtype = H ⊓ (P : Subgroup G) := by
    rw [hS_eq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hS_le_P : (S : Subgroup ↥H).map H.subtype ≤ (P : Subgroup G) := by
    rw [hS_map]; exact inf_le_right
  -- `U ≤ S` (as `U.subgroupOf H ≤ S`), so `Z(P)` image ⊆ image of S.
  have hU_le_HP : U ≤ H ⊓ (P : Subgroup G) := le_inf hU_le_H (OddOrder.Isaacs.Ch01.opCore_le P)
  -- `Z(P).map P.subtype ≤ U` (Step 1a).
  have hZP_le_U : (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤ U :=
    center_sylow_le_opCore_of_oPiCorePrime_eq_bot h_oPiPrime_trivial P
  -- Abbreviation: `ZS := Z(S).map S.subtype` (subgroup of `↥H`), `ZSG := ZS.map H.subtype`.
  set ZS : Subgroup ↥H := (Subgroup.center (S : Subgroup ↥H)).map (S : Subgroup ↥H).subtype
    with hZS_def
  refine le_antisymm ?_ ?_
  · -- `C_H(ZS) ≤ S`.  Map to `G`: contained in `C_G(Z(P)-image) = P`, p-subgroup ⊇ S.
    -- Step (a): `Z(P).map P.subtype ≤ ZS.map H.subtype` (central elts of P, lying in S,
    -- are central in S).
    have hZPG_le_ZSG :
        (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
          ZS.map H.subtype := by
      rintro _ ⟨z, hz_center, rfl⟩
      -- `(z : G) ∈ U ≤ H ⊓ P`, so `z` corresponds to an element of `S`.
      have hzG_U : ((z : (P : Subgroup G)) : G) ∈ U :=
        hZP_le_U ⟨z, hz_center, rfl⟩
      have hzG_H : ((z : (P : Subgroup G)) : G) ∈ H := hU_le_H hzG_U
      have hzG_P : ((z : (P : Subgroup G)) : G) ∈ (P : Subgroup G) := z.property
      -- `z` as element of `↥H`.
      set zH : ↥H := ⟨((z : (P : Subgroup G)) : G), hzG_H⟩ with hzH_def
      have hzH_S : zH ∈ (S : Subgroup ↥H) := by
        rw [hS_eq, Subgroup.mem_subgroupOf]
        exact ⟨hzG_H, hzG_P⟩
      -- `zH` is central in `S`: it commutes with every element of `S` (via `z ∈ Z(P)`, `S ≤ P`).
      have hzH_center : (⟨zH, hzH_S⟩ : (S : Subgroup ↥H)) ∈
          Subgroup.center (S : Subgroup ↥H) := by
        rw [Subgroup.mem_center_iff]
        intro s
        -- `s : ↥(S:Subgroup ↥H)`, its image in `G` lies in `P`.
        have hsG_P : (((s : (S : Subgroup ↥H)) : ↥H) : G) ∈ (P : Subgroup G) := by
          have hmem : (((s : (S : Subgroup ↥H)) : ↥H) : G) ∈
              (S : Subgroup ↥H).map H.subtype :=
            Subgroup.mem_map_of_mem H.subtype s.property
          exact hS_le_P hmem
        apply Subtype.ext; apply Subtype.ext
        -- `z` central in `P` commutes with `s`-image: `s_G * z_G = z_G * s_G`.
        have hcomm := Subgroup.mem_center_iff.mp hz_center
          (⟨(((s : (S : Subgroup ↥H)) : ↥H) : G), hsG_P⟩ : (P : Subgroup G))
        have hval := congrArg (fun x : (P : Subgroup G) => (x : G)) hcomm
        -- Goal (after two `Subtype.ext`): `s_G * z_G = z_G * s_G`.
        simpa [hzH_def] using hval
      -- So `zH.val (in G) ∈ ZS.map H.subtype`.
      exact ⟨zH, ⟨⟨zH, hzH_S⟩, hzH_center, rfl⟩, rfl⟩
    -- Step (b): `(C_H(ZS)).map H.subtype ≤ C_G(ZS.map H.subtype)`.
    have hcent_map :
        (Subgroup.centralizer (ZS : Set ↥H)).map H.subtype ≤
          Subgroup.centralizer ((ZS.map H.subtype) : Set G) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hcomm : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc w hw).symm
      exact congrArg (fun x : ↥H => (x : G)) hcomm.symm
    -- Combine: `(C_H(ZS)).map H.subtype ≤ C_G(Z(P)-image) = P`.
    have hcent_le_P : (Subgroup.centralizer (ZS : Set ↥H)).map H.subtype ≤ (P : Subgroup G) := by
      refine hcent_map.trans ?_
      have hmono : Subgroup.centralizer ((ZS.map H.subtype) : Set G) ≤
          Subgroup.centralizer
            (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
        Subgroup.centralizer_le hZPG_le_ZSG
      rw [h_centralizer_center] at hmono
      exact hmono
    -- `C_H(ZS) ≤ P.subgroupOf H` (a `p`-group), containing the Sylow `S` ⇒ equal.
    have hcent_le_Psub :
        Subgroup.centralizer (ZS : Set ↥H) ≤ (P : Subgroup G).subgroupOf H := by
      intro c hc
      rw [Subgroup.mem_subgroupOf]
      have : (c : G) ∈ (P : Subgroup G) := hcent_le_P ⟨c, hc, rfl⟩
      exact this
    have hPsub_pg : IsPGroup p ↥((P : Subgroup G).subgroupOf H) :=
      P.isPGroup'.comap_subtype
    have hcent_pg : IsPGroup p ↥(Subgroup.centralizer (ZS : Set ↥H)) :=
      hPsub_pg.of_injective (Subgroup.inclusion hcent_le_Psub)
        (Subgroup.inclusion_injective hcent_le_Psub)
    -- `S ≤ C_H(ZS)` (next bullet), so the Sylow `S` is inside the `p`-subgroup `C_H(ZS)`.
    have hS_le_cent : (S : Subgroup ↥H) ≤ Subgroup.centralizer (ZS : Set ↥H) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hcomm : (⟨s, hs⟩ : (S : Subgroup ↥H)) * w = w * ⟨s, hs⟩ :=
        Subgroup.mem_center_iff.mp hw ⟨s, hs⟩
      exact congrArg (fun x : (S : Subgroup ↥H) => (x : ↥H)) hcomm.symm
    exact (S.is_maximal' hcent_pg hS_le_cent).le
  · -- `S ≤ C_H(ZS)`: every `s ∈ S` centralizes `Z(S) ⊆ S`.
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hcomm : (⟨s, hs⟩ : (S : Subgroup ↥H)) * w = w * ⟨s, hs⟩ :=
      Subgroup.mem_center_iff.mp hw ⟨s, hs⟩
    exact congrArg (fun x : (S : Subgroup ↥H) => (x : ↥H)) hcomm.symm

end OddOrder.Isaacs.Ch07
