-- Prove2me | solution 1 for SimpleGraph.exists_perm_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:43.483728+00:00
-- url     : https://prove2.me/submissions/3fbc6ae1-1c7b-4b6d-a89f-58414d4290f9

module
public import Definitions.Def_Euler_Orientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card
public import Definitions.Def_Euler_Petersen

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution {D : Finset (V × V)} {k : ℕ} (hk : 0 < k)
    (hout : ∀ v, (D.filter fun p => p.1 = v).card = k)
    (hin : ∀ v, (D.filter fun p => p.2 = v).card = k) :
    ∃ σ : Equiv.Perm V, ∀ v, (v, σ v) ∈ D := by
  set t : V → Finset V := fun u => (D.filter fun p => p.1 = u).image Prod.snd
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion t).card := by
    intro s
    -- arcos que salen de `s`
    have h1 : (D.filter fun p => p.1 ∈ s).card = k * s.card := by
      have : (D.filter fun p => p.1 ∈ s) = s.biUnion fun u => D.filter fun p => p.1 = u := by
        ext p; simp only [mem_filter, mem_biUnion]
        constructor
        · rintro ⟨hp, hs⟩; exact ⟨p.1, hs, hp, rfl⟩
        · rintro ⟨u, hu, hp, rfl⟩; exact ⟨hp, hu⟩
      rw [this, card_biUnion fun x _ y _ hxy => disjoint_filter.mpr fun p _ h1 h2 =>
        hxy (h1.symm.trans h2)]
      rw [Finset.sum_congr rfl fun u _ => hout u, sum_const, smul_eq_mul, Nat.mul_comm]
    -- llegan a `N(s)`
    have h2 : (D.filter fun p => p.2 ∈ s.biUnion t).card = k * (s.biUnion t).card := by
      have : (D.filter fun p => p.2 ∈ s.biUnion t) =
          (s.biUnion t).biUnion fun w => D.filter fun p => p.2 = w := by
        ext p; simp only [mem_filter, mem_biUnion]
        constructor
        · rintro ⟨hp, hs⟩; exact ⟨p.2, hs, hp, rfl⟩
        · rintro ⟨w, hw, hp, rfl⟩; exact ⟨hp, hw⟩
      rw [this, card_biUnion fun x _ y _ hxy => disjoint_filter.mpr fun p _ h1 h2 =>
        hxy (h1.symm.trans h2)]
      rw [Finset.sum_congr rfl fun w _ => hin w, sum_const, smul_eq_mul, Nat.mul_comm]
    have h3 : (D.filter fun p => p.1 ∈ s) ⊆ D.filter fun p => p.2 ∈ s.biUnion t := by
      intro p hp
      obtain ⟨hpD, hps⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨hpD, mem_biUnion.mpr ⟨p.1, hps, ?_⟩⟩
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hpD, rfl⟩, rfl⟩
    have := card_le_card h3
    rw [h1, h2] at this
    exact Nat.le_of_mul_le_mul_left this hk
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  refine ⟨Equiv.ofBijective f hbij, fun v => ?_⟩
  obtain ⟨p, hp, hpv⟩ := mem_image.mp (hft v)
  obtain ⟨hpD, hp1⟩ := mem_filter.mp hp
  have : p = (v, f v) := Prod.ext hp1 hpv
  simpa [this] using hpD
end SimpleGraph
