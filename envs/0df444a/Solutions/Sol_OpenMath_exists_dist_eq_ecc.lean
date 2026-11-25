-- Prove2me | solution 1 for OpenMath.exists_dist_eq_ecc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:15.46683+00:00
-- url     : https://prove2.me/submissions/82849fd9-9e40-4ea7-b980-de27ff49786e

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
theorem _root_.solution {G : SimpleGraph α} (h : G.Connected) (u : α) :
    ∃ w, G.dist u w = ecc G u := by
  obtain ⟨w0, hw0⟩ := G.exists_edist_eq_eccent_of_finite u
  refine ⟨w0, ?_⟩
  unfold ecc
  rw [← hw0, ← (h.preconnected u w0).coe_dist_eq_edist, ENat.toNat_natCast]
end OpenMath
