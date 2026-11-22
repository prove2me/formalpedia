-- Prove2me | solution 1 for ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T06:40:58.884014+00:00
-- url     : https://prove2.me/submissions/a31fd01b-1523-4353-b940-f5e64be4c943

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

theorem solution {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l) :
    (c.map List.length).sum ≤ depth c * n := by
  classical
  -- Step 1: every instruction touches at least one wire.
  have hsupp : ∀ g : Instr n, g.support.Nonempty := by
    intro g
    cases g <;> simp [Instr.support]
  -- Choose a representative wire for each gate.
  obtain ⟨f, hf⟩ : ∃ f : Instr n → Fin n, ∀ g : Instr n, f g ∈ g.support :=
    ⟨fun g => (hsupp g).choose, fun g => (hsupp g).choose_spec⟩
  -- Step 2: the per-layer bound, via injectivity of the representative map on a layer.
  have hwidth : ∀ l : List (Instr n), LayerOk l → l.length ≤ n := by
    intro l hl
    have hpair : l.Pairwise (fun a b : Instr n => f a ≠ f b) := by
      refine hl.imp ?_
      intro a b hab heq
      have hmem : f a ∈ b.support := by rw [heq]; exact hf b
      exact Finset.disjoint_left.1 hab (hf a) hmem
    have hnodup : (l.map f).Nodup := List.pairwise_map.2 hpair
    calc l.length = (l.map f).length := by simp
      _ ≤ Fintype.card (Fin n) := hnodup.length_le_card
      _ = n := Fintype.card_fin n
  -- Step 3: sum over layers, by induction on the layer list.
  have key : ∀ d : Layered n, (∀ l ∈ d, LayerOk l) →
      (d.map List.length).sum ≤ depth d * n := by
    intro d
    induction d with
    | nil => intro _; simp [depth]
    | cons l t ih =>
        intro hd
        have h1 : l.length ≤ n := hwidth l (hd l (by simp))
        have h2 : (t.map List.length).sum ≤ depth t * n :=
          ih (fun l' hl' => hd l' (by simp [hl']))
        have hdep : depth (l :: t) = depth t + 1 := by simp [depth]
        rw [List.map_cons, List.sum_cons, hdep, add_mul, one_mul]
        calc l.length + (t.map List.length).sum
            ≤ n + depth t * n := add_le_add h1 h2
          _ = depth t * n + n := by ring
  exact key c hc
