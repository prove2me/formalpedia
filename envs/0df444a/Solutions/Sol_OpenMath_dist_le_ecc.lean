-- Prove2me | solution 1 for OpenMath.dist_le_ecc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:13.734901+00:00
-- url     : https://prove2.me/submissions/5ada2497-c9c3-48be-91d8-eb1328e85cdc

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
theorem _root_.solution {G : SimpleGraph α} (h : G.Connected) (u w : α) : G.dist u w ≤ ecc G u := by
  obtain ⟨w0, hw0⟩ := G.exists_edist_eq_eccent_of_finite u
  have hle : G.edist u w ≤ G.eccent u := by
    rw [eccent_def]
    exact le_iSup (fun v => G.edist u v) w
  rw [← hw0, ← (h.preconnected u w).coe_dist_eq_edist,
    ← (h.preconnected u w0).coe_dist_eq_edist] at hle
  unfold ecc
  rw [← hw0, ← (h.preconnected u w0).coe_dist_eq_edist, ENat.toNat_natCast]
  exact_mod_cast hle
end OpenMath
