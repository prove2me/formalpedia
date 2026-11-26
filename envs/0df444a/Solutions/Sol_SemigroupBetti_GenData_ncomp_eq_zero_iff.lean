-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:43.601894+00:00
-- url     : https://prove2.me/submissions/191b3eea-db59-428b-9503-ce5cca71a500

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} : G.ncomp d = 0 ↔ G.fiber d = ∅ := by
  unfold ncomp
  rw [Fintype.card_eq_zero_iff, ← Finset.isEmpty_coe_sort]
  constructor
  · intro h; exact ⟨fun v => h.false ((G.nabla d).connectedComponentMk v)⟩
  · intro h; infer_instance
end SemigroupBetti.GenData
