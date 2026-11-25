-- Prove2me | solution 1 for Robbins.not_rev_of_isPath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:23:27.767727+00:00
-- url     : https://prove2.me/submissions/a359c11f-64fb-4d65-b710-b83daeae4e63

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Robbins
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace Robbins
theorem _root_.solution {H : SimpleGraph V} {a b : V} {q : H.Walk a b} (hq : q.IsPath)
    {d₁ d₂ : H.Dart} (h₁ : d₁ ∈ q.darts) (h₂ : d₂ ∈ q.darts) (hf : d₁.fst = d₂.snd)
    (hs : d₁.snd = d₂.fst) : False := by
  have hsymm : d₂ = d₁.symm := by
    ext
    · exact hs.symm
    · exact hf.symm
  have hnd : (q.darts.map Dart.edge).Nodup := by
    rw [← Walk.edges_eq_map_darts]; exact hq.isTrail.edges_nodup
  have heq : d₁ = d₂ := List.inj_on_of_nodup_map hnd h₁ h₂ (by rw [hsymm, Dart.edge_symm])
  exact Dart.symm_ne d₁ (by rw [← hsymm, heq])
end Robbins
