-- Prove2me | solution 1 for TwinWidthI.BoolWidth.exists_same_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:35:04.453551+00:00
-- url     : https://prove2.me/submissions/1ce8534f-a14f-4f47-a4de-c91a7095112f

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

set_option autoImplicit false
open Finset TwinWidthI.BoolWidth

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) (hAB : Disjoint A B) (N : ℕ)
    (hcount : nbhdCount G A B ≤ N) (hA : N + 1 ≤ #A) :
    ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ ∀ b ∈ B, (G.Adj u b ↔ G.Adj v b) := by
  classical
  let f : V → Finset V := fun a => B.filter (fun b => G.Adj a b)
  have hmaps : ∀ a ∈ A, f a ∈ A.powerset.image (fun S => B.filter (fun b => ∃ a ∈ S, G.Adj a b)) := by
    intro a ha
    rw [Finset.mem_image]
    refine ⟨{a}, Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 ha), ?_⟩
    ext b
    simp [f]
  have hlt : (A.powerset.image (fun S => B.filter (fun b => ∃ a ∈ S, G.Adj a b))).card < #A := by
    have : (A.powerset.image (fun S => B.filter (fun b => ∃ a ∈ S, G.Adj a b))).card ≤ N := hcount
    omega
  obtain ⟨u, hu, v, hv, huv, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨u, hu, v, hv, huv, fun b hb => ?_⟩
  have := congrArg (fun S => b ∈ S) h
  simpa [f, hb] using this
