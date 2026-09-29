-- Prove2me | solution 1 for Wolf.fg_quotient_lcs
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:22:26.976564+00:00
-- url     : https://prove2.me/submissions/2bd6ed75-14ba-46fe-a2b2-a4ab66e6dce3

import Definitions.Def_MilnorWolf_Growth
import Mathlib

set_option autoImplicit false

open MilnorWolf
open scoped commutatorElement

namespace Ag4Aux_WolfFG

theorem three_mod {G : Type*} [Group G] (H₁ H₂ H₃ N : Subgroup G) [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have key : ∀ K : Subgroup G, K ≤ N ↔ K.map (QuotientGroup.mk' N) = ⊥ := by
    intro K; rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem aux {G : Type*} [Group G] (l : ℕ) :
    ∀ k : ℕ, ⁅MilnorWolf.lcs G k, MilnorWolf.lcs G l⁆ ≤ MilnorWolf.lcs G (k + l + 1) := by
  induction l with
  | zero => intro k; exact le_rfl
  | succ l ih =>
    intro k
    show ⁅lcs G k, ⁅lcs G l, ⊤⁆⁆ ≤ lcs G (k + (l + 1) + 1)
    rw [Subgroup.commutator_comm (lcs G k)]
    apply three_mod
    · have h := ih (k + 1)
      rw [show k + 1 + l + 1 = k + (l + 1) + 1 by omega] at h
      rw [Subgroup.commutator_comm ⊤ (lcs G k)]
      exact h
    · have h := Subgroup.commutator_mono (ih k) (le_refl (⊤ : Subgroup G))
      rw [show k + (l + 1) + 1 = (k + l + 1) + 1 by omega]
      exact h

theorem fg_of_cover {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (S : Finset G) (hS : (S : Set G) ⊆ (H : Set G)) (hle : H ≤ Subgroup.closure (S : Set G) ⊔ N) :
    Group.FG (H ⧸ N.subgroupOf H) := by
  classical
  rw [Group.fg_iff]
  let A : Set H := Subtype.val ⁻¹' (S : Set G)
  refine ⟨(QuotientGroup.mk' (N.subgroupOf H)) '' A, ?_,
    (S.finite_toSet.preimage Subtype.val_injective.injOn).image _⟩
  have hH : Subgroup.map H.subtype ⊤ = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htop : Subgroup.closure A ⊔ N.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, hH,
      inf_eq_left.mpr hNH]
    have hA : (H.subtype '' A) = (S : Set G) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨⟨x, hS hx⟩, hx, rfl⟩
    rw [hA]
    apply le_antisymm
    · exact sup_le ((Subgroup.closure_le _).mpr hS) hNH
    · exact hle
  rw [← MonoidHom.map_closure]
  have h2 : Subgroup.map (QuotientGroup.mk' (N.subgroupOf H)) (Subgroup.closure A ⊔ N.subgroupOf H)
      = ⊤ := by
    rw [htop, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  have h3 : Subgroup.map (QuotientGroup.mk' (N.subgroupOf H)) (N.subgroupOf H) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, h3, sup_bot_eq] at h2
  exact h2

theorem base {G : Type*} [Group G]
    (hfg : Group.FG (↥(MilnorWolf.lcs G 0) ⧸ (MilnorWolf.lcs G 1).subgroupOf (MilnorWolf.lcs G 0))) :
    ∃ T : Finset G, (⊤ : Subgroup G) ≤ Subgroup.closure (T : Set G) ⊔ lcs G 1 := by
  classical
  rw [Group.fg_iff] at hfg
  obtain ⟨S0, hcl, hfin⟩ := hfg
  let ψ := QuotientGroup.mk' ((lcs G 1).subgroupOf (lcs G 0))
  refine ⟨hfin.toFinset.image (fun q => ((Quotient.out q : lcs G 0) : G)), ?_⟩
  let W : Subgroup (lcs G 0) :=
    (Subgroup.closure ((hfin.toFinset.image (fun q => ((Quotient.out q : lcs G 0) : G)) : Finset G) :
      Set G) ⊔ lcs G 1).subgroupOf (lcs G 0)
  have hker : ψ.ker ≤ W := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (le_sup_right : lcs G 1 ≤ _) hx
  have hmap : (⊤ : Subgroup _) ≤ W.map ψ := by
    rw [← hcl, Subgroup.closure_le]
    intro q hq
    refine ⟨Quotient.out q, ?_, QuotientGroup.out_eq' q⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    apply (le_sup_left : Subgroup.closure _ ≤ _)
    apply Subgroup.subset_closure
    simp only [Finset.coe_image, Set.Finite.coe_toFinset]
    exact ⟨q, hq, rfl⟩
  have hW : W = ⊤ := by
    rw [← Subgroup.comap_map_eq_self hker]
    exact top_le_iff.mp (le_trans (le_of_eq (Subgroup.comap_top ψ).symm) (Subgroup.comap_mono hmap))
  intro g _
  have : (⟨g, Subgroup.mem_top g⟩ : lcs G 0) ∈ W := by rw [hW]; exact Subgroup.mem_top _
  exact this

theorem step {G : Type*} [Group G] (k : ℕ) (T : Finset G)
    (hT : (⊤ : Subgroup G) ≤ Subgroup.closure (T : Set G) ⊔ lcs G 1)
    (S : Finset G) (hS : (S : Set G) ⊆ (lcs G k : Set G))
    (hSk : lcs G k ≤ Subgroup.closure (S : Set G) ⊔ lcs G (k + 1)) :
    ∃ S' : Finset G, (S' : Set G) ⊆ (lcs G (k + 1) : Set G) ∧
      lcs G (k + 1) ≤ Subgroup.closure (S' : Set G) ⊔ lcs G (k + 2) := by
  classical
  let S' : Finset G := (S ×ˢ T).image (fun p => ⁅p.1, p.2⁆)
  refine ⟨S', ?_, ?_⟩
  · intro x hx
    simp only [S', Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx
    obtain ⟨⟨s, t⟩, ⟨hs, _⟩, rfl⟩ := hx
    exact Subgroup.commutator_mem_commutator (hS hs) (Subgroup.mem_top t)
  let N := lcs G (k + 2)
  let K : Subgroup G := Subgroup.closure (S' : Set G) ⊔ N
  have hNK : N ≤ K := le_sup_right
  have hN : ∀ c ∈ lcs G (k + 1), ∀ g : G, ⁅g, c⁆ ∈ N := by
    intro c hc g
    show ⁅g, c⁆ ∈ ⁅lcs G (k + 1), ⊤⁆
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hc
  have hmem1 : ∀ a ∈ lcs G k, ∀ g : G, ⁅a, g⁆ ∈ lcs G (k + 1) := fun a ha g =>
    Subgroup.commutator_mem_commutator ha (Subgroup.mem_top g)
  have hlt : lcs G (k + 1) ≤ lcs G k :=
    Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (Nat.le_succ k)
  have hγ1 : ∀ a ∈ lcs G k, ∀ g ∈ lcs G 1, ⁅a, g⁆ ∈ N := by
    intro a ha g hg
    have := aux (G := G) 1 k
    exact this (Subgroup.commutator_mem_commutator ha hg)
  have hγk1 : ∀ a ∈ lcs G (k + 1), ∀ g : G, ⁅a, g⁆ ∈ N := fun a ha g =>
    Subgroup.commutator_mem_commutator ha (Subgroup.mem_top g)
  -- multiplicativity in the second slot
  have hmulG : ∀ a ∈ lcs G k, ∀ g g' : G, ⁅a, g⁆ ∈ K → ⁅a, g'⁆ ∈ K → ⁅a, g * g'⁆ ∈ K := by
    intro a ha g g' h1 h2
    have e : ⁅a, g * g'⁆ = ⁅a, g⁆ * ⁅g, ⁅a, g'⁆⁆ * ⁅a, g'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (K.mul_mem h1 (hNK (hN _ (hmem1 a ha g') g))) h2
  have hinvG : ∀ a ∈ lcs G k, ∀ g : G, ⁅a, g⁆ ∈ K → ⁅a, g⁻¹⁆ ∈ K := by
    intro a ha g h1
    have e : ⁅a, g⁻¹⁆ = ⁅g⁻¹, ⁅a, g⁆⁻¹⁆ * ⁅a, g⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (hNK (hN _ ((lcs G (k + 1)).inv_mem (hmem1 a ha g)) _)) (K.inv_mem h1)
  have hmulA : ∀ a ∈ lcs G k, ∀ a' ∈ lcs G k, ∀ g : G, ⁅a, g⁆ ∈ K → ⁅a', g⁆ ∈ K →
      ⁅a * a', g⁆ ∈ K := by
    intro a ha a' ha' g h1 h2
    have e : ⁅a * a', g⁆ = ⁅a, ⁅a', g⁆⁆ * ⁅a', g⁆ * ⁅a, g⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (hNK (hN _ (hmem1 a' ha' g) a)) h2) h1
  have hinvA : ∀ a ∈ lcs G k, ∀ g : G, ⁅a, g⁆ ∈ K → ⁅a⁻¹, g⁆ ∈ K := by
    intro a ha g h1
    have e : ⁅a⁻¹, g⁆ = ⁅a⁻¹, ⁅a, g⁆⁻¹⁆ * ⁅a, g⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (hNK (hN _ ((lcs G (k + 1)).inv_mem (hmem1 a ha g)) _)) (K.inv_mem h1)
  -- step 1
  have step1 : ∀ s ∈ S, ∀ g : G, ⁅s, g⁆ ∈ K := by
    intro s hs
    have hsk : s ∈ lcs G k := hS hs
    let Q : Subgroup G :=
      { carrier := {g | ⁅s, g⁆ ∈ K}
        mul_mem' := fun {g g'} h1 h2 => hmulG s hsk g g' h1 h2
        one_mem' := by simp
        inv_mem' := fun {g} h1 => hinvG s hsk g h1 }
    have hTQ : Subgroup.closure (T : Set G) ⊔ lcs G 1 ≤ Q := by
      apply sup_le
      · rw [Subgroup.closure_le]
        intro t ht
        show ⁅s, t⁆ ∈ K
        apply (le_sup_left : Subgroup.closure (S' : Set G) ≤ K)
        apply Subgroup.subset_closure
        simp only [S', Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
        exact ⟨(s, t), ⟨hs, ht⟩, rfl⟩
      · intro g hg
        exact hNK (hγ1 s hsk g hg)
    intro g
    exact hTQ (hT (Subgroup.mem_top g))
  have step2 : ∀ a ∈ lcs G k, ∀ g : G, ⁅a, g⁆ ∈ K := by
    intro a ha g
    let P : Subgroup G :=
      { carrier := {a | a ∈ lcs G k ∧ ⁅a, g⁆ ∈ K}
        mul_mem' := fun {a a'} h1 h2 =>
          ⟨(lcs G k).mul_mem h1.1 h2.1, hmulA a h1.1 a' h2.1 g h1.2 h2.2⟩
        one_mem' := ⟨(lcs G k).one_mem, by simp⟩
        inv_mem' := fun {a} h1 => ⟨(lcs G k).inv_mem h1.1, hinvA a h1.1 g h1.2⟩ }
    have hSP : Subgroup.closure (S : Set G) ⊔ lcs G (k + 1) ≤ P := by
      apply sup_le
      · rw [Subgroup.closure_le]
        intro s hs
        exact ⟨hS hs, step1 s hs g⟩
      · intro c hc
        exact ⟨hlt hc, hNK (hγk1 c hc g)⟩
    exact (hSP (hSk ha)).2
  show ⁅lcs G k, ⊤⁆ ≤ K
  rw [Subgroup.commutator_le]
  intro a ha g _
  exact step2 a ha g

end Ag4Aux_WolfFG

open Ag4Aux_WolfFG in
theorem solution {G : Type*} [Group G] (hfg : Group.FG (↥(MilnorWolf.lcs G 0) ⧸ (MilnorWolf.lcs G 1).subgroupOf (MilnorWolf.lcs G 0))) (k : ℕ) : Group.FG (↥(MilnorWolf.lcs G k) ⧸ ((MilnorWolf.lcs G (k + 1)).subgroupOf (MilnorWolf.lcs G k))) := by
  obtain ⟨T, hT⟩ := base hfg
  have P : ∀ k : ℕ, ∃ S : Finset G, (S : Set G) ⊆ (lcs G k : Set G) ∧
      lcs G k ≤ Subgroup.closure (S : Set G) ⊔ lcs G (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨T, fun x _ => Subgroup.mem_top x, hT⟩
    | succ k ih =>
      obtain ⟨S, hS, hSk⟩ := ih
      exact step k T hT S hS hSk
  obtain ⟨S, hS, hSk⟩ := P k
  exact fg_of_cover (lcs G k) (lcs G (k + 1))
    (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (Nat.le_succ k)) S hS hSk
