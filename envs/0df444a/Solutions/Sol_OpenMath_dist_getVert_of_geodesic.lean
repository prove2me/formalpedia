-- Prove2me | solution 1 for OpenMath.dist_getVert_of_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:12.198977+00:00
-- url     : https://prove2.me/submissions/81104596-d69d-42b5-bfb0-3e809b2ae418

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
public import Definitions.Def_OpenMath_Common

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath
theorem _root_.solution {G : SimpleGraph α} (h : G.Connected) {u w : α}
    (p : G.Walk u w) (hp : p.length = G.dist u w) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by
  have h1 : G.dist u (p.getVert i) ≤ i := by
    have := dist_le (p.take i)
    rw [Walk.take_length] at this
    omega
  have h2 : G.dist (p.getVert i) w ≤ p.length - i := by
    have := dist_le (p.drop i)
    rwa [Walk.drop_length] at this
  have h3 : G.dist u w ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) w := h.dist_triangle
  omega
end OpenMath
