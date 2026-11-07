-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.rooted_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:15:47.042879+00:00
-- url     : https://prove2.me/submissions/2468eb6c-871c-4268-b92a-49a8d84f9905

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_rooted

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (r : V) : rooted G r 1 = {{r}} := by
  classical
  have hc : (G.induce (({r} : Finset V) : Set V)).Connected := by
    letI : Nonempty {x : V // x ∈ ({r} : Finset V)} := ⟨⟨r,by simp⟩⟩
    letI : Subsingleton {x : V // x ∈ ({r} : Finset V)} := ⟨by
      intro x y
      apply Subtype.ext
      exact (Finset.mem_singleton.mp x.property).trans (Finset.mem_singleton.mp y.property).symm⟩
    exact SimpleGraph.Connected.of_subsingleton
  ext A
  rw [mem_rooted,Finset.mem_singleton]
  constructor
  · rintro ⟨hr,hm,hconnected⟩
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hm
    rw [ha] at hr
    have hra : r = a := Finset.mem_singleton.mp hr
    simpa only [hra] using ha
  · intro he
    subst A
    exact ⟨by simp,by simp,hc⟩
end QEC.Locality.ConnectedSetCounting
