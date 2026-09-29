-- Prove2me | solution 1 for R03SP08NativeBridgeless.no_bridge_of_threeVertexConnected_cubic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:17.146636+00:00
-- url     : https://prove2.me/submissions/696ac2ab-9853-4854-a1c9-9dbbe776ec8c

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_117d348ee0_SP08_NATIVE_BRIDGELESS_FROM_3CONN_CUBIC_v1

/-!
Candidate-only native graph lemma.  It derives absence of native graph
bridges from the exact frozen ThreeVertexConnected and Cubic predicates.  It
is deliberately independent of planarity, rotation systems, source
hypermaps, and the Four-Colour theorem.
-/

namespace R03SP08NativeBridgeless

open CubicP3Partition

universe u
variable {V : Type u} [Fintype V]

lemma neighbor_ncard_of_cubic {G : SimpleGraph V}
    (hcubic : Cubic G) (u : V) : (G.neighborSet u).ncard = 3 := by
  have hu := hcubic u
  change Nat.card {w : V // G.Adj u w} = 3 at hu
  change (G.neighborSet u).ncard = 3
  change Nat.card (G.neighborSet u) = 3
  rw [Nat.card_coe_set_eq]
  exact hu

lemma exists_neighbor_ne_of_cubic {G : SimpleGraph V}
    (hcubic : Cubic G) {u v : V} (huv : G.Adj u v) :
    ∃ w, G.Adj u w ∧ w ≠ v := by
  have hn : (G.neighborSet u).ncard = 3 := neighbor_ncard_of_cubic hcubic u
  have hv : v ∈ G.neighborSet u := (G.mem_neighborSet u v).2 huv
  have hlt : ({v} : Set V).ncard < (G.neighborSet u).ncard := by
    simp [hn]
  obtain ⟨w, hw, hwv⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({v} : Set V)) (t := G.neighborSet u) hlt
  exact ⟨w, (G.mem_neighborSet u w).1 hw, by simpa using hwv⟩

lemma induced_singleton_connected {G : SimpleGraph V}
    (hconn : ThreeVertexConnected G) (u : V) :
    (G.induce {v : V | v ∉ ({u} : Finset V)}).Connected := by
  exact hconn.2 {u} (by simp)


end R03SP08NativeBridgeless

open R03SP08NativeBridgeless
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
    {G : SimpleGraph V} (hconn : ThreeVertexConnected G)
    (hcubic : Cubic G) {u v : V} (huv : G.Adj u v) :
    ¬ G.IsBridge s(u, v) := by
  intro hbridge
  obtain ⟨w, huw, hwv⟩ := exists_neighbor_ne_of_cubic hcubic huv
  have hdel := induced_singleton_connected hconn u
  have hvdel : v ∈ ({x : V | x ∉ ({u} : Finset V)} : Set V) := by
    simpa only [Set.mem_ofPred_eq, Finset.mem_singleton] using huv.ne.symm
  have hwdel : w ∈ ({x : V | x ∉ ({u} : Finset V)} : Set V) := by
    simpa only [Set.mem_ofPred_eq, Finset.mem_singleton] using huw.ne.symm
  obtain ⟨p⟩ := hdel.preconnected ⟨w, hwdel⟩ ⟨v, hvdel⟩
  let pG : G.Walk w v :=
    p.map (SimpleGraph.Embedding.induce ({x : V | x ∉ ({u} : Finset V)})).toHom
  let q : G.Walk u v := .cons huw pG
  have hq : s(u, v) ∈ q.edges :=
    (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hbridge) q
  have hpu : u ∉ pG.support := by
    intro hu_mem
    change u ∈ (p.map (SimpleGraph.Embedding.induce
      ({x : V | x ∉ ({u} : Finset V)})).toHom).support at hu_mem
    rw [SimpleGraph.Walk.support_map] at hu_mem
    simp only [List.mem_map] at hu_mem
    obtain ⟨z, hz, hzu⟩ := hu_mem
    exact z.property (by simpa using hzu)
  have hfirst : s(u, v) ≠ s(u, w) := by
    intro h
    rcases (Sym2.eq_iff.mp h) with ⟨_, hvw⟩ | ⟨huw', hvu'⟩
    · exact hwv hvw.symm
    · exact huv.ne (hvu'.symm)
  have hq_edges : q.edges = s(u, w) :: pG.edges := by rfl
  have hq' : s(u, v) = s(u, w) ∨ s(u, v) ∈ pG.edges := by
    simpa [hq_edges] using hq
  rcases hq' with hq | hq
  · exact hfirst hq
  · have hmem : u ∈ pG.support :=
      SimpleGraph.Walk.mem_support_of_mem_edges hq (by
        rw [Sym2.mem_iff]
        exact Or.inl rfl)
    exact hpu hmem
