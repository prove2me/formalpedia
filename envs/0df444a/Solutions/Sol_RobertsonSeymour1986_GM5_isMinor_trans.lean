-- Prove2me | solution 1 for RobertsonSeymour1986.GM5.isMinor_trans
-- status  : ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-18T12:50:54.959205+00:00
-- url     : https://prove2.me/submissions/2b773f46-b97c-41de-9875-07023f9f89bd

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

open SimpleGraph

theorem solution {W U V : Type} {H : SimpleGraph W} {K : SimpleGraph U} {G : SimpleGraph V}
    (hHK : RobertsonSeymour1986.GM5.IsMinor H K) (hKG : RobertsonSeymour1986.GM5.IsMinor K G) :
    RobertsonSeymour1986.GM5.IsMinor H G := by
  obtain ⟨β₁, hβ₁, hd₁, ha₁⟩ := hHK
  obtain ⟨β₂, hβ₂, hd₂, ha₂⟩ := hKG
  let γ : W → Set V := fun w => ⋃ u ∈ β₁ w, β₂ u
  have mem_γ : ∀ {w u x}, u ∈ β₁ w → x ∈ β₂ u → x ∈ γ w := fun hu hx =>
    Set.mem_biUnion hu hx
  refine ⟨γ, fun w => ?_, ?_, ?_⟩
  · -- nonempty and connected
    obtain ⟨u₀, hu₀⟩ := (hβ₁ w).1
    obtain ⟨x₀, hx₀⟩ := (hβ₂ u₀).1
    have hx₀γ : x₀ ∈ γ w := mem_γ hu₀ hx₀
    refine ⟨⟨x₀, hx₀γ⟩, ?_⟩
    -- every vertex of `β₂ u` (for `u ∈ β₁ w`) is reachable from `x₀` inside `γ w`
    let P : β₁ w → Prop := fun u => ∀ x (hx : x ∈ β₂ u.1),
      (G.induce (γ w)).Reachable ⟨x₀, hx₀γ⟩ ⟨x, mem_γ u.2 hx⟩
    -- reachability inside one branch set `β₂ u`
    have inside : ∀ (u : β₁ w) {a x} (ha : a ∈ β₂ u.1) (hx : x ∈ β₂ u.1),
        (G.induce (γ w)).Reachable ⟨a, mem_γ u.2 ha⟩ ⟨x, mem_γ u.2 hx⟩ := by
      intro u a x ha hx
      have hsub : β₂ u.1 ⊆ γ w := fun y hy => mem_γ u.2 hy
      exact ((hβ₂ u.1).2 ⟨a, ha⟩ ⟨x, hx⟩).map (induceHomOfLE G hsub).toHom
    have P₀ : P ⟨u₀, hu₀⟩ := fun x hx => inside ⟨u₀, hu₀⟩ hx₀ hx
    have step : ∀ u v : β₁ w, (K.induce (β₁ w)).Adj u v → P u → P v := by
      intro u v huv hPu x hx
      obtain ⟨a, ha, b, hb, hab⟩ := ha₂ u.1 v.1 huv
      have e : (G.induce (γ w)).Adj ⟨a, mem_γ u.2 ha⟩ ⟨b, mem_γ v.2 hb⟩ := hab
      exact ((hPu a ha).trans e.reachable).trans (inside v hb hx)
    have walk : ∀ (u v : β₁ w) (p : (K.induce (β₁ w)).Walk u v), P u → P v := by
      intro u v p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun hu => ih (step _ _ h hu)
    have hall : ∀ y : γ w, (G.induce (γ w)).Reachable ⟨x₀, hx₀γ⟩ y := by
      rintro ⟨x, hx⟩
      have hx' := hx
      rw [Set.mem_iUnion₂] at hx'
      obtain ⟨u, hu, hxu⟩ := hx'
      obtain ⟨p⟩ := (hβ₁ w).2 ⟨u₀, hu₀⟩ ⟨u, hu⟩
      exact walk _ _ p P₀ x hxu
    haveI : Nonempty (γ w) := ⟨⟨x₀, hx₀γ⟩⟩
    exact ⟨fun y z => (hall y).symm.trans (hall z)⟩
  · -- disjointness
    intro w w' hww'
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_iUnion₂] at hx hx'
    obtain ⟨u, hu, hxu⟩ := hx
    obtain ⟨u', hu', hxu'⟩ := hx'
    by_cases huu : u = u'
    · subst huu
      exact Set.disjoint_left.mp (hd₁ hww') hu hu'
    · exact Set.disjoint_left.mp (hd₂ huu) hxu hxu'
  · -- adjacency
    intro a b hab
    obtain ⟨u, hu, u', hu', huu'⟩ := ha₁ a b hab
    obtain ⟨x, hx, y, hy, hxy⟩ := ha₂ u u' huu'
    exact ⟨x, mem_γ hu hx, y, mem_γ hu' hy, hxy⟩
