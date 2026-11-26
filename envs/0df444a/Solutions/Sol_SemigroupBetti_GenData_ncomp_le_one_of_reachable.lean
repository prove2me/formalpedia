-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_le_one_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:36.17181+00:00
-- url     : https://prove2.me/submissions/b5376eaa-b1c3-4bc4-b700-524f5134e10d

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
theorem _root_.solution {d : ℕ} (h : ∀ z y : G.fiber d, (G.nabla d).Reachable z y) :
    G.ncomp d ≤ 1 := by
  unfold ncomp
  rw [Fintype.card_le_one_iff_subsingleton]
  exact ⟨SimpleGraph.ConnectedComponent.ind₂ fun v w =>
    SimpleGraph.ConnectedComponent.sound (h v w)⟩
end SemigroupBetti.GenData
