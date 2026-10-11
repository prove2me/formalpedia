-- Prove2me | solution 1 for PrimAnalysis.prim_complete
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T01:15:43.846982+00:00
-- url     : https://prove2.me/submissions/57c5f82c-664e-4512-9594-9e5c7723c86b

import Definitions.Def_Algo_prim_prim_Analysis


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Local execution rules for Prim's two loops. Each lemma describes public
    named locations and source variables. Queue calls are supplied as contracts;
    their representation and balancing details do not enter these proofs. -/

namespace PrimControl

open Algo2LeanCore Algo2LeanGenerated
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim
open Algo.dijkstra.priority_queue





variable (dependencies : Dependencies)









/-- An empty adjacency list exits the loop without changing the heap. -/
theorem scan_empty (heap : Heap) (queue : ObjectRef) (key parent selected : SeqRef) (vertex : Int) :
    ScanLoop dependencies heap queue key parent selected vertex none heap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_false _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc2 _ _ caller)
    exact Reaches.single (Step.scan_edges_pc1 _ _ caller)

/-- A selected target is skipped; the loop continues at the next adjacency cell. -/
theorem scan_selected (heap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex target : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readNext : field_Edge_next heap edge = some next)
    (already : heap.read selected target ≠ 0)
    (tail : ScanLoop dependencies (heap.tick "edges") queue key parent selected vertex next finalHeap) :
    ScanLoop dependencies heap queue key parent selected vertex (some edge) finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc21 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller valid.2.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc18_false _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using already))
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- An unselected target whose edge key cannot improve leaves the queue unchanged. -/
theorem scan_unimproved (heap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next heap edge = some next)
    (unselected : heap.read selected target = 0)
    (discovered : 0 ≤ heap.read parent target)
    (notBetter : heap.read key target ≤ weight)
    (tail : ScanLoop dependencies (heap.tick "edges") queue key parent selected vertex next finalHeap) :
    ScanLoop dependencies heap queue key parent selected vertex (some edge) finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc21 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller valid.2.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc18_true _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using unselected))
    apply Reaches.prepend (Step.scan_edges_pc17 _ _ caller
      (by simp [field__a2l_import_0_Edge_weight, readWeight]))
    apply Reaches.prepend (Step.scan_edges_pc16 _ _ caller
      ⟨valid.2.2.1, fun _ => valid.2.1⟩)
    apply Reaches.prepend (Step.scan_edges_pc15_false _ _ caller
      (by simp [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight, readTarget, readWeight]; omega))
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller

/-- A successful key improvement reuses the abstract queue Call and then resumes the loop. -/
theorem scan_improved (heap queuedHeap finalHeap : Heap) (queue : ObjectRef) (key parent selected : SeqRef)
    (vertex target weight : Int) (edge : Ref_Edge) (next : Option Ref_Edge)
    (valid : scan_edges.ValidInput dependencies heap (queue,key,parent,selected,vertex,some edge))
    (readTarget : field_Edge_target heap edge = some target)
    (readWeight : field_Edge_weight heap edge = some weight)
    (readNext : field_Edge_next queuedHeap edge = some next)
    (unselected : heap.read selected target = 0)
    (better : heap.read parent target < 0 ∨ weight < heap.read key target)
    (update : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue
      ((((heap.tick "edges").write key target weight).write parent target vertex).tick "queue_updates")
      (queue,target,weight) queuedHeap ())
    (tail : ScanLoop dependencies (queuedHeap.tick "improvements") queue key parent selected vertex next finalHeap) :
    ScanLoop dependencies heap queue key parent selected vertex (some edge) finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameQueue, sameKey, sameParent, sameSelected, sameVertex, sameEdge⟩ := located
    unfold scan_edges.At.scan at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent, scan_edges.Local.selected,
      scan_edges.Local.vertex, scan_edges.Local.edge] at sameQueue sameKey sameParent sameSelected sameVertex sameEdge
    subst_vars
    intro caller
    apply Reaches.prepend (Step.scan_edges_pc4 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.scan_edges_pc21 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc20 _ _ caller (by simp [field__a2l_import_0_Edge_target, readTarget]))
    apply Reaches.prepend (Step.scan_edges_pc19 _ _ caller valid.2.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc18_true _ _ caller (by simpa [field__a2l_import_0_Edge_target, readTarget] using unselected))
    apply Reaches.prepend (Step.scan_edges_pc17 _ _ caller
      (by simp [field__a2l_import_0_Edge_weight, readWeight]))
    apply Reaches.prepend (Step.scan_edges_pc16 _ _ caller
      ⟨valid.2.2.1, fun _ => valid.2.1⟩)
    apply Reaches.prepend (Step.scan_edges_pc15_true _ _ caller
      (by simpa [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight, readTarget,readWeight] using better))
    simp only [field__a2l_import_0_Edge_target, field__a2l_import_0_Edge_weight,
      edge_target_tick, edge_weight_tick, readTarget, readWeight, Option.getD_some]
    apply Reaches.prepend (Step.scan_edges_pc14 _ _ caller valid.2.1)
    apply Reaches.prepend (Step.scan_edges_pc13 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.scan_edges_pc12 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc11 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc10 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue, Heap.read, Heap.tick] using update.1))
    apply Reaches.prepend (Step.scan_edges_pc9 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc8 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc7 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller update.2).trans
    apply Reaches.prepend (Step.scan_edges_pc6 _ _ caller)
    apply Reaches.prepend (Step.scan_edges_pc5 _ _ caller (by simp [field__a2l_import_0_Edge_next, readNext]))
    exact tail (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge,
        Config.heap, field__a2l_import_0_Edge_next, readNext]) caller



/-- The final empty test returns the parent reference. -/
theorem extract_empty (heap : Heap) (graph : Ref_Graph) (queue : ObjectRef) (key parent selected : SeqRef)
    (parentAllocated : parent < heap.nextRef)
    (empty : PriorityQueue.is_empty.Call dependencies.PriorityQueue
      (heap.tick "queue_empty_checks") queue (heap.tick "queue_empty_checks") true) :
    ExtractLoop dependencies heap graph queue key parent selected (heap.tick "queue_empty_checks") := by
  open Algo.prim.prim.Algo2LeanGenerated in
    intro state located
    obtain ⟨named, sameHeap, sameGraph, sameQueue, sameKey, sameParent, sameSelected⟩ := located
    unfold prim.At.extract at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [prim.Local.graph, prim.Local.queue, prim.Local.key, prim.Local.parent,
      prim.Local.selected] at sameGraph sameQueue sameKey sameParent sameSelected
    subst_vars
    intro caller
    apply Reaches.prepend (Step.prim_pc7 _ _ caller)
    apply Reaches.prepend (Step.prim_pc6 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using empty.1))
    apply Reaches.prepend (Step.prim_pc5 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller empty.2).trans
    apply Reaches.prepend (Step.prim_pc4 _ _ caller)
    apply Reaches.prepend (Step.prim_pc3_false _ _ caller rfl)
    apply Reaches.prepend (Step.prim_pc2 _ _ caller)
    exact Reaches.single (Step.prim_pc1 _ _ caller parentAllocated)

/-- One extraction composes the queue contract, adjacency-loop contract, and
    next iteration. Caller frames and irrelevant locals remain encapsulated. -/
theorem extract_next (heap poppedHeap scannedHeap finalHeap : Heap)
    (graph : Ref_Graph) (queue : ObjectRef) (key parent selected : SeqRef) (vertex : Int)
    (heads : CollectionRef) (head : Option Ref_Edge)
    (empty : PriorityQueue.is_empty.Call dependencies.PriorityQueue
      (heap.tick "queue_empty_checks") queue (heap.tick "queue_empty_checks") false)
    (popped : PriorityQueue.pop_min.Call dependencies.PriorityQueue
      ((heap.tick "queue_empty_checks").tick "queue_pops") queue poppedHeap vertex)
    (selectedAllocated : selected < poppedHeap.nextRef)
    (readHeads : field_Graph_heads poppedHeap graph = some heads)
    (readHead : seq_Edge_optional.get poppedHeap heads vertex = some head)
    (scan : ScanLoop dependencies ((poppedHeap.write selected vertex 1).tick "settlements")
      queue key parent selected vertex head scannedHeap)
    (tail : ExtractLoop dependencies scannedHeap graph queue key parent selected finalHeap) :
    ExtractLoop dependencies heap graph queue key parent selected finalHeap := by
  open Algo.prim.prim.Algo2LeanGenerated in
    have headsAfter : field__a2l_import_0_Graph_heads
        ((poppedHeap.write selected vertex 1).tick "settlements") graph = some heads := readHeads
    have headAfter : seq__a2l_import_0_Edge_optional.get
        ((poppedHeap.write selected vertex 1).tick "settlements") heads vertex = some head := readHead
    intro state located
    obtain ⟨named, sameHeap, sameGraph, sameQueue, sameKey, sameParent, sameSelected⟩ := located
    unfold prim.At.extract at named
    split at named <;> try contradiction
    rename_i currentHeap locals stack
    simp only [Config.heap] at sameHeap
    subst currentHeap
    cases locals
    simp [prim.Local.graph, prim.Local.queue, prim.Local.key, prim.Local.parent,
      prim.Local.selected] at sameGraph sameQueue sameKey sameParent sameSelected
    subst_vars
    intro caller
    apply Reaches.prepend (Step.prim_pc7 _ _ caller)
    apply Reaches.prepend (Step.prim_pc6 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using empty.1))
    apply Reaches.prepend (Step.prim_pc5 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller empty.2).trans
    apply Reaches.prepend (Step.prim_pc4 _ _ caller)
    apply Reaches.prepend (Step.prim_pc3_true _ _ caller rfl)
    apply Reaches.prepend (Step.prim_pc22 _ _ caller)
    apply Reaches.prepend (Step.prim_pc21 _ _ caller)
    apply Reaches.prepend (Step.prim_pc20 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using popped.1))
    apply Reaches.prepend (Step.prim_pc19 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller popped.2).trans
    apply Reaches.prepend (Step.prim_pc18 _ _ caller)
    apply Reaches.prepend (Step.prim_pc17 _ _ caller selectedAllocated)
    apply Reaches.prepend (Step.prim_pc16 _ _ caller)
    apply Reaches.prepend (Step.prim_pc15 _ _ caller)
    apply Reaches.prepend (Step.prim_pc14 _ _ caller)
    apply Reaches.prepend (Step.prim_pc13 _ _ caller)
    apply Reaches.prepend (Step.prim_pc12 _ _ caller)
    apply Reaches.prepend (Step.prim_pc11 _ _ caller)
    apply Reaches.prepend (Step.prim_pc10 _ _ caller (by simp [headsAfter,headAfter]))
    apply Reaches.prepend (Step.prim_pc9 _ _ caller)
    simp only [headsAfter,headAfter,Option.getD_some]
    apply Reaches.trans (scan (.active _ (.fn_scan_edges 4 _) [])
      (by simp [AtScan, scan_edges.At.scan, scan_edges.Local.queue, scan_edges.Local.key, scan_edges.Local.parent,
        scan_edges.Local.selected, scan_edges.Local.vertex, scan_edges.Local.edge, Config.heap]) _)
    apply Reaches.prepend (Step.prim_pc8 _ _ caller)
    exact tail (.active _ (.fn_prim 7 _) [])
      (by simp [AtExtract, prim.At.extract, prim.Local.graph, prim.Local.queue,
        prim.Local.key, prim.Local.parent, prim.Local.selected, Config.heap]) caller

/-- Initialization adds the root once and enters the main loop. -/
theorem initialize_summary (heap queuedHeap finalHeap : Heap) (graph : Ref_Graph) (root : Int)
    (queue : ObjectRef) (key parent selected : SeqRef)
    (valid : prim.ValidInput dependencies heap (graph,root,queue,key,parent,selected))
    (inserted : PriorityQueue.push_or_decrease.Call dependencies.PriorityQueue
      ((heap.write key root 0).tick "queue_updates") (queue,root,0) queuedHeap ())
    (tail : ExtractLoop dependencies queuedHeap graph queue key parent selected finalHeap) :
    prim.Call dependencies heap (graph,root,queue,key,parent,selected) finalHeap parent := by
  open Algo.prim.prim.Algo2LeanGenerated in
    refine ⟨valid, ?_⟩
    intro caller
    apply Reaches.prepend (Step.prim_pc30 _ _ caller valid.2.2.1)
    apply Reaches.prepend (Step.prim_pc29 _ _ caller)
    apply Reaches.prepend (Step.prim_pc28 _ _ caller)
    apply Reaches.prepend (Step.prim_pc27 _ _ caller (by simpa [is__a2l_import_1_PriorityQueue] using inserted.1))
    apply Reaches.prepend (Step.prim_pc26 _ _ caller)
    apply Reaches.prepend (Step.prim_pc25 _ _ caller)
    apply Reaches.prepend (Step.prim_pc24 _ _ caller)
    apply (ModuleCall.summary (interface_PriorityQueue_simulates dependencies) _ caller inserted.2).trans
    apply Reaches.prepend (Step.prim_pc23 _ _ caller)
    exact tail (.active _ (.fn_prim 7 _) [])
      (by simp [AtExtract, prim.At.extract, prim.Local.graph, prim.Local.queue,
        prim.Local.key, prim.Local.parent, prim.Local.selected, Config.heap]) caller


end PrimControl

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Reusable shortest-path mathematics for Dijkstra implementations.

This module imports neither a compiled algorithm nor the Algo2Lean runtime.
Distance sequences are ordinary functions `Int → Int`. A queue backend only
needs to supply minimum selection, the relaxation scan, and exhaustion; the
path, frontier, and shortest-distance proofs are shared across backends.
-/

namespace Algo2Lean.Dijkstra





































theorem vertexRange_nodup (size : Int) : (vertexRange size).Nodup := by
  exact List.Pairwise.map Int.ofNat (fun a b different same => different (Int.ofNat.inj same)) List.nodup_range





/-- Each settlement consumes exactly one remaining vertex. -/
theorem remaining_length (remaining : List Int) (selected : Int) (member : selected ∈ remaining) :
    (remaining.erase selected).length + 1 = remaining.length := by
  have positive := List.length_pos_of_mem member
  rw [List.length_erase_of_mem member]
  omega







/-- Removing one list entry removes exactly its contribution to any natural
    weighted sum. This does not need a no-duplicates assumption. -/
theorem weighted_sum_erase (weight : Int → Nat) (remaining : List Int) (selected : Int)
    (member : selected ∈ remaining) :
    ((remaining.erase selected).map weight).sum + weight selected = (remaining.map weight).sum := by
  induction remaining with
  | nil => simp at member
  | cons vertex rest ih =>
    by_cases same : selected = vertex
    · subst selected
      simp [Nat.add_comm]
    · have inRest : selected ∈ rest := by simpa [same] using member
      have shorter := ih inRest
      simpa [List.erase_cons, same, Ne.symm same, Nat.add_assoc] using
        congrArg (fun total => weight vertex + total) shorter

theorem edgeBudget_erase (adjacency : Adjacency) (remaining : List Int) (selected : Int)
    (member : selected ∈ remaining) :
    edgeBudget adjacency (remaining.erase selected) + (adjacency selected).length =
      edgeBudget adjacency remaining :=
  weighted_sum_erase (fun vertex => (adjacency vertex).length) remaining selected member











/-! Pure invariants for every iteration of Dijkstra, independent of the queue
implementation, storage layout, and compiler-generated transition system. -/

































































/-! Backend-independent queue and complete-loop contracts. -/



























end Algo2Lean.Dijkstra

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal







theorem Adjacent.symm {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Adjacent edges v u := by
  obtain ⟨e, member, forward | backward⟩ := edge
  · exact ⟨e, member, Or.inr forward⟩
  · exact ⟨e, member, Or.inl backward⟩

theorem Adjacent.connected {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Connected edges u v := .step edge (.refl _)

theorem Connected.trans {edges : List Edge} {u v w : Int}
    (first : Connected edges u v) (second : Connected edges v w) : Connected edges u w := by
  induction first with
  | refl => exact second
  | step edge path ih => exact .step edge (ih second)

theorem Connected.symm {edges : List Edge} {u v : Int} (path : Connected edges u v) :
    Connected edges v u := by
  induction path with
  | refl => exact .refl _
  | step edge path ih => exact ih.trans edge.symm.connected

theorem Connected.mono {before after : List Edge} {u v : Int}
    (subset : ∀ edge ∈ before, edge ∈ after) (path : Connected before u v) :
    Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step edge path ih =>
    obtain ⟨e, member, direction⟩ := edge
    exact .step ⟨e, subset e member, direction⟩ ih

theorem Connected.replace {before after : List Edge} {u v : Int}
    (edges : ∀ edge ∈ before, Connected after edge.source edge.target)
    (path : Connected before u v) : Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step adjacent path ih =>
    obtain ⟨edge, member, forward | backward⟩ := adjacent
    · obtain ⟨rfl, rfl⟩ := forward
      exact (edges edge member).trans ih
    · obtain ⟨rfl, rfl⟩ := backward
      exact (edges edge member).symm.trans ih



theorem edge_connected {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    Connected edges edge.source edge.target :=
  Adjacent.connected ⟨edge, member, Or.inl ⟨rfl, rfl⟩⟩

/-- A walk between opposite sides of a cut contains a crossing edge. -/
theorem Connected.crosses_cut {edges : List Edge} {u v : Int} (side : Int → Prop)
    (path : Connected edges u v) (inside : side u) (outside : ¬ side v) :
    ∃ edge ∈ edges,
      (side edge.source ∧ ¬ side edge.target) ∨
      (side edge.target ∧ ¬ side edge.source) := by
  classical
  induction path with
  | refl => exact False.elim (outside inside)
  | @step u next v adjacent rest ih =>
    by_cases same : side next
    · exact ih same outside
    · obtain ⟨edge, member, forward | backward⟩ := adjacent
      · obtain ⟨rfl, rfl⟩ := forward
        exact ⟨edge, member, Or.inl ⟨inside, same⟩⟩
      · obtain ⟨rfl, rfl⟩ := backward
        exact ⟨edge, member, Or.inr ⟨inside, same⟩⟩






























theorem Joined.trans {edges : List Edge} {a b u v w : Int}
    (one : Joined edges a b u v) (two : Joined edges a b v w) :
    Joined edges a b u w := by
  rcases one with old | forward | backward
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inl (old.trans oldTwo)
    · exact Or.inr (Or.inl ⟨old.trans forwardTwo.1, forwardTwo.2⟩)
    · exact Or.inr (Or.inr ⟨old.trans backwardTwo.1, backwardTwo.2⟩)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inl ⟨forward.1, forward.2.trans oldTwo⟩)
    · exact Or.inr (Or.inl ⟨forward.1, forwardTwo.2⟩)
    · exact Or.inl (forward.1.trans backwardTwo.2)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inr ⟨backward.1, backward.2.trans oldTwo⟩)
    · exact Or.inl (backward.1.trans forwardTwo.2)
    · exact Or.inr (Or.inr ⟨backward.1, backwardTwo.2⟩)

theorem connected_cons {edge : Edge} {edges : List Edge} {u v : Int} :
    Connected (edge :: edges) u v ↔ Joined edges edge.source edge.target u v := by
  constructor
  · intro path
    induction path with
    | refl => exact Or.inl (.refl _)
    | @step u next v adjacent rest ih =>
      apply Joined.trans (v := next) ?_ ih
      obtain ⟨candidate, member, direction⟩ := adjacent
      rcases List.mem_cons.mp member with rfl | member
      · rcases direction with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _, .refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _, .refl _⟩)
      · exact Or.inl (Adjacent.connected ⟨candidate, member, direction⟩)
  · intro joined
    have lift {x y} (path : Connected edges x y) : Connected (edge :: edges) x y :=
      path.mono (fun _ member => List.mem_cons_of_mem edge member)
    rcases joined with old | forward | backward
    · exact lift old
    · exact (lift forward.1).trans ((edge_connected (by simp)).trans (lift forward.2))
    · exact (lift backward.1).trans ((edge_connected (by simp)).symm.trans (lift backward.2))

/-- An inserted forest edge cannot already occur in the remaining list. -/
theorem Forest.fresh {edge : Edge} {edges : List Edge} (forest : Forest (edge :: edges)) :
    edge ∉ edges := by
  intro member
  exact forest.2 (edge_connected member)



/-- Joining different components cannot create an alternate route inside an
    existing component, even after some of that component's edges are removed. -/
theorem disconnected_extension {edge : Edge} {before after : List Edge} {u v : Int}
    (subset : ∀ candidate ∈ after, candidate ∈ before)
    (separate : ¬ Connected before edge.source edge.target)
    (old : Connected before u v) (path : Connected (edge :: after) u v) :
    Connected after u v := by
  rcases connected_cons.mp path with unchanged | forward | backward
  · exact unchanged
  · exact False.elim (separate ((forward.1.mono subset).symm.trans
      (old.trans (forward.2.mono subset).symm)))
  · exact False.elim (separate ((backward.2.mono subset).trans
      (old.symm.trans (backward.1.mono subset))))


/-- Deleting an edge preserves acyclicity. -/
theorem Forest.erase {edges : List Edge} (forest : Forest edges) (removed : Edge) :
    Forest (edges.erase removed) := by
  induction edges with
  | nil => trivial
  | cons edge rest ih =>
    by_cases same : edge = removed
    · subst edge; simpa using forest.1
    · simp only [List.erase_cons, beq_iff_eq, same, ↓reduceIte]
      exact ⟨ih forest.1, fun path => forest.2
        (path.mono (fun _ member => List.mem_of_mem_erase member))⟩

/-- Every edge of a forest is a bridge. -/
theorem Forest.bridge {edges : List Edge} (forest : Forest edges)
    {edge : Edge} (member : edge ∈ edges) :
    ¬ Connected (edges.erase edge) edge.source edge.target := by
  induction edges with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simpa using forest.2
    · have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp only [List.erase_cons, beq_iff_eq, different, ↓reduceIte]
      intro path
      exact ih forest.1 member (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2
        (edge_connected member) path)

/-- A forest path can be reconstructed from the edges whose deletion separates
    its endpoints. This avoids choosing a particular list representation of a path. -/
theorem Forest.essential_cover {edges selected : List Edge} (forest : Forest edges)
    {u v : Int} (path : Connected edges u v)
    (contains : ∀ edge ∈ edges, ¬ Connected (edges.erase edge) u v → edge ∈ selected) :
    Connected selected u v := by
  classical
  induction edges generalizing u v with
  | nil => exact connected_nil.mp path ▸ Connected.refl u
  | cons first rest ih =>
    have removed {edge : Edge} (member : edge ∈ rest) :
        (first :: rest).erase edge = first :: rest.erase edge := by
      have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp [different]
    by_cases old : Connected rest u v
    · apply ih forest.1 old
      intro edge member necessary
      apply contains edge (by simp [member])
      rw [removed member]
      intro alternative
      exact necessary (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2 old alternative)
    · have join (x y : Int) (left : Connected rest x first.source)
          (right : Connected rest first.target y) (separate : ¬ Connected rest x y)
          (covered : ∀ edge ∈ first :: rest,
            ¬ Connected ((first :: rest).erase edge) x y → edge ∈ selected) :
          Connected selected x y := by
        have selectedFirst : first ∈ selected := covered first (by simp) (by simpa)
        have selectedLeft : Connected selected x first.source := by
          apply ih forest.1 left
          intro edge member necessary
          apply covered edge (by simp [member])
          rw [removed member]
          intro alternative
          rcases connected_cons.mp alternative with unchanged | forward | backward
          · exact separate (unchanged.mono (fun _ included => List.mem_of_mem_erase included))
          · exact necessary forward.1
          · exact forest.2 (left.symm.trans
              (backward.1.mono (fun _ included => List.mem_of_mem_erase included)))
        have selectedRight : Connected selected first.target y := by
          apply ih forest.1 right
          intro edge member necessary
          apply covered edge (by simp [member])
          rw [removed member]
          intro alternative
          rcases connected_cons.mp alternative with unchanged | forward | backward
          · exact separate (unchanged.mono (fun _ included => List.mem_of_mem_erase included))
          · exact necessary forward.2
          · exact forest.2 ((backward.2.mono
              (fun _ included => List.mem_of_mem_erase included)).trans right.symm)
        exact selectedLeft.trans ((edge_connected selectedFirst).trans selectedRight)
      rcases connected_cons.mp path with impossible | forward | backward
      · exact False.elim (old impossible)
      · exact join u v forward.1 forward.2 old contains
      · apply Connected.symm
        apply join v u backward.2.symm backward.1.symm (fun p => old p.symm)
        intro edge member necessary
        exact contains edge member (fun p => necessary p.symm)

/-- If a smaller edge set fails to connect a pair, some essential edge of a
    connecting forest is missing from that set. -/
theorem Forest.missing_bridge {edges selected : List Edge} (forest : Forest edges)
    {u v : Int} (path : Connected edges u v) (separate : ¬ Connected selected u v) :
    ∃ edge ∈ edges, edge ∉ selected ∧ ¬ Connected (edges.erase edge) u v := by
  classical
  apply Classical.byContradiction
  intro absent
  apply separate
  apply forest.essential_cover path
  intro edge member necessary
  apply Classical.byContradiction
  intro missing
  exact absent ⟨edge, member, missing, necessary⟩

/-- Exchanging a bridge on the new edge's path preserves all connected components. -/
theorem exchange_connectivity {edges : List Edge} {added removed : Edge}
    (member : removed ∈ edges) (linked : Connected edges added.source added.target)
    (separate : ¬ Connected (edges.erase removed) added.source added.target) :
    ∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v := by
  have permutation := List.perm_cons_erase member
  have existing : Connected (removed :: edges.erase removed) added.source added.target :=
    linked.mono (fun _ present => permutation.mem_iff.mp present)
  have removedLinked : Connected (added :: edges.erase removed) removed.source removed.target := by
    have lift {x y} (path : Connected (edges.erase removed) x y) :
        Connected (added :: edges.erase removed) x y :=
      path.mono (fun _ present => List.mem_cons_of_mem added present)
    have addedLinked : Connected (added :: edges.erase removed) added.source added.target :=
      edge_connected (by simp)
    rcases connected_cons.mp existing with impossible | forward | backward
    · exact False.elim (separate impossible)
    · exact (lift forward.1).symm.trans (addedLinked.trans (lift forward.2).symm)
    · exact (lift backward.2).trans (addedLinked.symm.trans (lift backward.1))
  intro u v
  constructor
  · intro path
    apply path.replace
    intro edge present
    rcases List.mem_cons.mp present with rfl | present
    · exact linked
    · exact edge_connected (List.mem_of_mem_erase present)
  · intro path
    apply path.replace
    intro edge present
    by_cases same : edge = removed
    · subst edge; exact removedLinked
    · exact edge_connected (by simp [((List.mem_erase_of_ne same).mpr present)])







theorem weight_perm {one two : List Edge} (same : one.Perm two) : weight one = weight two := by
  induction same with
  | nil => rfl
  | cons edge same ih => simp [ih]
  | swap first second rest => simp [Int.add_left_comm]
  | trans first second ihOne ihTwo => exact ihOne.trans ihTwo

theorem weight_erase {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    weight edges = edge.weight + weight (edges.erase edge) :=
  (weight_perm (List.perm_cons_erase member)).trans (weight_cons edge _)

/-- A forest edge not in a selected subgraph cannot have its endpoints already
    connected by that subgraph: otherwise it would not be a bridge. -/
theorem Forest.outside_disconnected {edges selected : List Edge} (forest : Forest edges)
    (subset : ∀ edge ∈ selected, edge ∈ edges) {edge : Edge}
    (member : edge ∈ edges) (missing : edge ∉ selected) :
    ¬ Connected selected edge.source edge.target := by
  intro path
  apply forest.bridge member
  apply path.mono
  intro candidate present
  have different : candidate ≠ edge := by intro same; exact missing (same ▸ present)
  exact (List.mem_erase_of_ne different).mpr (subset candidate present)

/-- Forests with exactly the same edge occurrences have the same total weight. -/
theorem Forest.weight_eq {one two : List Edge} (first : Forest one) (second : Forest two)
    (same : ∀ edge, edge ∈ one ↔ edge ∈ two) : weight one = weight two := by
  induction one generalizing two with
  | nil =>
    cases two with
    | nil => rfl
    | cons edge rest => have absent := (same edge).mpr (by simp); simp at absent
  | cons edge rest ih =>
    have present : edge ∈ two := (same edge).mp (by simp)
    have deleted : edge ∉ two.erase edge := by
      intro member
      exact second.bridge present (edge_connected member)
    have remaining : ∀ candidate, candidate ∈ rest ↔ candidate ∈ two.erase edge := by
      intro candidate
      constructor
      · intro member
        have different : candidate ≠ edge := by intro equal; exact first.fresh (equal ▸ member)
        exact (List.mem_erase_of_ne different).mpr ((same candidate).mp (by simp [member]))
      · intro member
        rcases List.mem_cons.mp ((same candidate).mpr (List.mem_of_mem_erase member)) with equal | present
        · exact False.elim (deleted (equal ▸ member))
        · exact present
    rw [weight_cons, weight_erase present, ih first.1 (second.erase edge) remaining]


























theorem MinimumSpanningForest.tree {size : Nat} {input selected : List Edge}
    (minimum : MinimumSpanningForest input selected) (nonempty : 0 < size)
    (valid : ValidInput size input) (connected : ConnectedOn size input) :
    MinimumSpanningTree size input selected := by
  refine ⟨nonempty, valid, minimum, ?_⟩
  intro u v uLower uUpper vLower vUpper
  exact minimum.2.1.connected u v (connected u v uLower uUpper vLower vUpper)



end Algo2Lean.Kruskal

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Representation and preservation of finite adjacency lists with signed weights. -/
namespace PrimGraph
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated











theorem AdjacencyChain.preserved {before after : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain before size head edges)
    (unchanged : EdgeFieldsUnchanged before after) : AdjacencyChain after size head edges := by
  induction chain with
  | empty => exact .empty
  | cons edge target weight next tail valid readTarget readWeight readNext nonnegative bound chain ih =>
    obtain ⟨newValid, targetSame, weightSame, nextSame⟩ := unchanged edge valid
    exact .cons edge target weight next tail newValid (targetSame.trans readTarget)
      (weightSame.trans readWeight) (nextSame.trans readNext) nonnegative bound ih


theorem AdjacencyChain.member_valid {heap : Heap} {size : Int} {head : Option Ref_Edge}
    {edges : List (Int × Int)} (chain : AdjacencyChain heap size head edges)
    (target weight : Int) (member : (target, weight) ∈ edges) :
    0 ≤ target ∧ target < size := by
  induction chain with
  | empty => simp at member
  | cons edge first firstWeight next tail valid readTarget readWeight readNext lower upper chain ih =>
    simp only [List.mem_cons] at member
    rcases member with same | remaining
    · cases same
      exact ⟨lower, upper⟩
    · exact ih remaining



theorem GraphFrame.refl (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef) :
    GraphFrame heap heap graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩

theorem GraphFrame.trans {first middle last : Heap} {graph : Ref_Graph} {heads : CollectionRef}
    (one : GraphFrame first middle graph heads) (two : GraphFrame middle last graph heads) :
    GraphFrame first last graph heads := by
  refine ⟨fun valid => two.valid (one.valid valid), two.size.trans one.size,
    two.headsField.trans one.headsField, fun valid => two.headsValid (one.headsValid valid),
    fun vertex => (two.entries vertex).trans (one.entries vertex), ?_⟩
  intro ref valid
  obtain ⟨middleValid, firstTarget, firstWeight, firstNext⟩ := one.edges ref valid
  obtain ⟨lastValid, secondTarget, secondWeight, secondNext⟩ := two.edges ref middleValid
  exact ⟨lastValid, secondTarget.trans firstTarget, secondWeight.trans firstWeight, secondNext.trans firstNext⟩

theorem GraphRep.preserved {before after : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep before graph size heads adjacency)
    (frame : GraphFrame before after graph heads) : GraphRep after graph size heads adjacency := by
  refine ⟨frame.valid representation.valid, representation.sizeNonnegative,
    frame.size.trans representation.readSize, frame.headsField.trans representation.readHeads,
    frame.headsValid representation.headsValid, ?_⟩
  intro vertex nonnegative bound
  obtain ⟨head, readHead, chain⟩ := representation.chains vertex nonnegative bound
  exact ⟨head, (frame.entries vertex).trans readHead, chain.preserved frame.edges⟩

theorem graph_frame_write (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (ref : SeqRef) (index value : Int) : GraphFrame heap (heap.write ref index value) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩



theorem graph_frame_tick (heap : Heap) (graph : Ref_Graph) (heads : CollectionRef)
    (clock : String) (amount : Nat) : GraphFrame heap (heap.tick clock amount) graph heads := by
  exact ⟨id, rfl, rfl, id, fun _ => rfl, fun _ valid => ⟨valid, rfl, rfl, rfl⟩⟩












theorem adjacencyEntries_member (size source target weight : Int) (adjacency : Adjacency) :
    (source, target, weight) ∈ adjacencyEntries size adjacency ↔
      0 ≤ source ∧ source < size ∧ (target, weight) ∈ adjacency source := by
  simp only [adjacencyEntries, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, member, entry, adjacent, sameSource, sameEntry⟩
    subst u
    subst entry
    exact ⟨(vertexRange_member size source).mp member |>.1,
      (vertexRange_member size source).mp member |>.2, adjacent⟩
  · rintro ⟨lower, upper, adjacent⟩
    exact ⟨source, (vertexRange_member size source).mpr ⟨lower, upper⟩,
      (target, weight), adjacent, rfl, rfl⟩

/-- Directed membership forgets only an occurrence's unique identity. -/
theorem inputEdges_member (size : Int) (adjacency : Adjacency) (source target weight : Int) :
    (∃ id, (⟨id, source, target, weight⟩ : Algo2Lean.Kruskal.Edge) ∈ inputEdges size adjacency) ↔
      0 ≤ source ∧ source < size ∧ (target, weight) ∈ adjacency source := by
  rw [← adjacencyEntries_member]
  constructor
  · rintro ⟨id, member⟩
    obtain ⟨⟨⟨u,v,w⟩, index⟩, included, same⟩ := List.mem_map.mp member
    cases same
    exact List.fst_mem_of_mem_zipIdx included
  · intro member
    obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
    refine ⟨index, List.mem_map.mpr ⟨((source,target,weight),index), ?_, rfl⟩⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr indexed

/-- Every represented occurrence gives the same directed adjacency observation. -/
theorem inputEdges_observation {size : Int} {adjacency : Adjacency}
    {edge : Algo2Lean.Kruskal.Edge} (member : edge ∈ inputEdges size adjacency) :
    0 ≤ edge.source ∧ edge.source < size ∧
      (edge.target, edge.weight) ∈ adjacency edge.source := by
  cases edge with
  | mk id source target weight => exact (inputEdges_member size adjacency source target weight).mp ⟨id, member⟩

/-- Occurrence identifiers are exactly a consecutive range, even for duplicate
    endpoint/weight triples and self-loops. -/
theorem inputEdges_identities (size : Int) (adjacency : Adjacency) :
    ((inputEdges size adjacency).map Algo2Lean.Kruskal.Edge.id).Nodup := by
  simpa only [inputEdges, List.map_map, Function.comp_def, List.zipIdx_map_snd] using
    List.nodup_range' (s := 0) (n := (adjacencyEntries size adjacency).length)



/-- A represented signed-weight graph supplies the finite mathematical graph's
    endpoint bounds and unique edge identities. -/
theorem GraphRep.validInput {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency) :
    Algo2Lean.Kruskal.ValidInput size.toNat (inputEdges size adjacency) := by
  refine ⟨inputEdges_identities size adjacency, ?_, ?_⟩
  · intro edge member
    obtain ⟨lower, upper, _⟩ := inputEdges_observation member
    exact ⟨lower, by omega⟩
  · intro edge member
    obtain ⟨lower, upper, adjacent⟩ := inputEdges_observation member
    obtain ⟨head, _, chain⟩ := representation.chains edge.source lower upper
    obtain ⟨nonnegative, bound⟩ := chain.member_valid edge.target edge.weight adjacent
    exact ⟨nonnegative, by omega⟩



/-- Symmetric adjacency lists give the reverse-edge witnesses needed by Prim's
    undirected cut argument. The reverse may have a different occurrence id. -/
theorem GraphRep.inputEdges_reverse {heap : Heap} {graph : Ref_Graph} {size : Int}
    {heads : CollectionRef} {adjacency : Adjacency}
    (representation : GraphRep heap graph size heads adjacency)
    (symmetric : Symmetric size adjacency) :
    ∀ edge ∈ inputEdges size adjacency,
      ∃ reverse ∈ inputEdges size adjacency,
        reverse.source = edge.target ∧ reverse.target = edge.source ∧
          reverse.weight = edge.weight := by
  intro edge member
  obtain ⟨lower, upper, adjacent⟩ := inputEdges_observation member
  obtain ⟨head, _, chain⟩ := representation.chains edge.source lower upper
  obtain ⟨targetLower, targetUpper⟩ := chain.member_valid edge.target edge.weight adjacent
  have reversed := symmetric edge.source edge.target edge.weight lower upper adjacent
  obtain ⟨id, included⟩ := (inputEdges_member size adjacency edge.target edge.source edge.weight).mpr
    ⟨targetLower, targetUpper, reversed⟩
  exact ⟨⟨id, edge.target, edge.source, edge.weight⟩, included, rfl, rfl, rfl⟩

end PrimGraph

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
The cut argument for Prim's minimum spanning tree algorithm. The graph and MST
definitions are shared with Kruskal: edge occurrences have identities, edges are
undirected, and weights are arbitrary integers. The proofs permit equal weights,
negative weights, loops, and parallel input occurrences.

`LightEdge` describes the only greedy choice required by Prim. `Safe.add_light`
shows that this choice preserves extendibility to a minimum spanning forest.
`Growth.minimum_spanning_tree` packages the complete mathematical argument;
an implementation proof only supplies the chosen cuts and final coverage.
-/

namespace Algo2Lean.Prim

open Algo2Lean.Kruskal







/-- A walk along edges that respect a cut cannot leave the side where it starts. -/
theorem stays_inside {edges : List Edge} {u v : Int} {inside : Int → Prop}
    (respects : Respects inside edges) (path : Connected edges u v)
    (start : inside u) : inside v := by
  classical
  induction path with
  | refl => exact start
  | @step u next v adjacent rest ih =>
    apply ih
    apply Classical.byContradiction
    intro outside
    obtain ⟨edge, member, forward | backward⟩ := adjacent
    · obtain ⟨rfl, rfl⟩ := forward
      exact respects edge member (Or.inl ⟨start, outside⟩)
    · obtain ⟨rfl, rfl⟩ := backward
      exact respects edge member (Or.inr ⟨start, outside⟩)

/-- Crossing endpoints cannot already be connected using edges respecting the cut. -/
theorem crossing_disconnected {edges : List Edge} {edge : Edge} {inside : Int → Prop}
    (respects : Respects inside edges) (crossing : Crosses inside edge) :
    ¬ Connected edges edge.source edge.target := by
  intro path
  rcases crossing with forward | backward
  · exact forward.2 (stays_inside respects path forward.1)
  · exact backward.2 (stays_inside respects path.symm backward.1)

/-- An edge crossing a cut can replace a crossing edge of a connecting forest.
The replacement preserves the forest's connected components exactly. -/
theorem exchange_across_cut {edges : List Edge} {added : Edge} {inside : Int → Prop}
    (forest : Forest edges) (linked : Connected edges added.source added.target)
    (crossing : Crosses inside added) :
    ∃ removed ∈ edges, Crosses inside removed ∧
      Forest (added :: edges.erase removed) ∧
      (∀ u v, Connected (added :: edges.erase removed) u v ↔ Connected edges u v) := by
  classical
  let internal := edges.filter (fun edge => decide (¬ Crosses inside edge))
  have respects : Respects inside internal := by
    intro edge member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  obtain ⟨removed, member, outside, necessary⟩ :=
    forest.missing_bridge linked (crossing_disconnected respects crossing)
  have removedCrossing : Crosses inside removed := by
    apply Classical.byContradiction
    intro absent
    exact outside (List.mem_filter.mpr ⟨member, by simp [absent]⟩)
  exact ⟨removed, member, removedCrossing, ⟨forest.erase removed, necessary⟩,
    exchange_connectivity member linked necessary⟩



theorem safe_nil (input : List Edge) : Safe input [] := by
  intro other forest spanning
  exact ⟨other, forest, spanning, by simp, Int.le_refl _⟩

/-- The light-edge theorem used by Prim: adding a least-weight edge across a
cut that respects all chosen edges preserves safety. -/
theorem Safe.add_light {input selected : List Edge} {edge : Edge} {inside : Int → Prop}
    (safe : Safe input selected) (light : LightEdge input inside edge)
    (respects : Respects inside selected) : Safe input (edge :: selected) := by
  classical
  intro other otherForest otherSpans
  obtain ⟨completion, forest, spanning, retains, bound⟩ := safe other otherForest otherSpans
  obtain ⟨removed, member, crossing, exchanged, connectivity⟩ :=
    exchange_across_cut forest
      (spanning.connected _ _ (edge_connected light.member)) light.crosses
  have missing : removed ∉ selected := fun present => respects removed present crossing
  have cheap := light.least removed (spanning.subset removed member) crossing
  refine ⟨edge :: completion.erase removed, exchanged, ?_, ?_, ?_⟩
  · constructor
    · intro candidate present
      rcases List.mem_cons.mp present with rfl | present
      · exact light.member
      · exact spanning.subset candidate (List.mem_of_mem_erase present)
    · intro u v path
      exact (connectivity u v).mpr (spanning.connected u v path)
  · intro candidate present
    rcases List.mem_cons.mp present with rfl | present
    · simp
    · have different : candidate ≠ removed := by
        intro same
        exact missing (same ▸ present)
      exact List.mem_cons_of_mem edge
        ((List.mem_erase_of_ne different).mpr (retains candidate present))
  · have cost : weight (edge :: completion.erase removed) ≤ weight completion := by
      rw [weight_cons, weight_erase member]
      omega
    exact Int.le_trans cost bound

/-- Once safe chosen edges span the input, they have minimum possible weight. -/
theorem Safe.minimum_spanning_forest {input selected : List Edge}
    (safe : Safe input selected) (forest : Forest selected) (spanning : Spans input selected) :
    MinimumSpanningForest input selected := by
  classical
  refine ⟨forest, spanning, ?_⟩
  intro other otherForest otherSpans
  obtain ⟨completion, completeForest, completeSpans, retains, bound⟩ :=
    safe other otherForest otherSpans
  have same : ∀ edge, edge ∈ selected ↔ edge ∈ completion := by
    intro edge
    refine ⟨retains edge, ?_⟩
    intro member
    apply Classical.byContradiction
    intro missing
    exact completeForest.outside_disconnected retains member missing
      (spanning.connected _ _ (edge_connected (completeSpans.subset edge member)))
  rw [forest.weight_eq completeForest same]
  exact bound











-- Main result: Correctness




/-- The single visited root and no selected edges satisfy Prim's tree invariant. -/
theorem TreeState.initial (input : List Edge) (root : Int) :
    TreeState input root (fun vertex => vertex = root) [] := by
  refine ⟨rfl, by simp, by simp, ?_, trivial, safe_nil input⟩
  intro vertex same
  subst vertex
  exact .refl root

theorem TreeState.respects {input selected : List Edge} {root : Int} {visited : Int → Prop}
    (state : TreeState input root visited selected) : Respects visited selected := by
  intro edge member crossing
  obtain ⟨sourceInside, targetInside⟩ := state.endpoints edge member
  rcases crossing with forward | backward
  · exact forward.2 targetInside
  · exact backward.2 sourceInside

/-- Selecting a light outgoing edge extends the current tree to its unvisited
target. This is the complete mathematical invariant step of Prim's main loop. -/
theorem TreeState.extend {input selected : List Edge} {root : Int} {visited : Int → Prop}
    (state : TreeState input root visited selected) {edge : Edge}
    (light : LightEdge input visited edge) (sourceInside : visited edge.source)
    (targetOutside : ¬ visited edge.target) :
    TreeState input root (fun vertex => visited vertex ∨ vertex = edge.target)
      (edge :: selected) := by
  have lift {u v : Int} (path : Connected selected u v) : Connected (edge :: selected) u v :=
    path.mono (fun _ member => List.mem_cons_of_mem edge member)
  refine ⟨Or.inl state.root_visited, ?_, ?_, ?_, ?_, state.safe.add_light light state.respects⟩
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact light.member
    · exact state.subset candidate member
  · intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Or.inl sourceInside, Or.inr rfl⟩
    · exact ⟨Or.inl (state.endpoints candidate member).1,
        Or.inl (state.endpoints candidate member).2⟩
  · intro vertex inside
    rcases inside with old | rfl
    · exact lift (state.reaches vertex old)
    · exact (lift (state.reaches edge.source sourceInside)).trans
        (edge_connected (by simp))
  · exact ⟨state.forest, fun path => targetOutside (stays_inside state.respects path sourceInside)⟩

/-- Changing only the representation of the visited set preserves the invariant. -/
theorem TreeState.congr_visited {input selected : List Edge} {root : Int}
    {before after : Int → Prop} (state : TreeState input root before selected)
    (same : ∀ vertex, before vertex ↔ after vertex) : TreeState input root after selected := by
  refine ⟨(same root).mp state.root_visited, state.subset, ?_, ?_, state.forest, state.safe⟩
  · intro edge member
    exact ⟨(same edge.source).mp (state.endpoints edge member).1,
      (same edge.target).mp (state.endpoints edge member).2⟩
  · intro vertex member
    exact state.reaches vertex ((same vertex).mpr member)

/-- Visiting every endpoint makes the selected tree span the whole input. -/
theorem TreeState.spans {input selected : List Edge} {root : Int} {visited : Int → Prop}
    (state : TreeState input root visited selected)
    (covered : ∀ edge ∈ input, visited edge.source ∧ visited edge.target) :
    Spans input selected := by
  refine ⟨state.subset, ?_⟩
  intro u v path
  apply path.replace
  intro edge member
  exact (state.reaches edge.source (covered edge member).1).symm.trans
    (state.reaches edge.target (covered edge member).2)

/-- Prim's completed tree has minimum weight among all spanning forests. -/
theorem TreeState.minimum_spanning_forest {input selected : List Edge} {root : Int}
    {visited : Int → Prop} (state : TreeState input root visited selected)
    (covered : ∀ edge ∈ input, visited edge.source ∧ visited edge.target) :
    MinimumSpanningForest input selected :=
  state.safe.minimum_spanning_forest state.forest (state.spans covered)

/-- Finishing the loop on a connected finite graph yields a genuine MST. The
only implementation-specific obligation is that every declared vertex was visited. -/
theorem TreeState.minimum_spanning_tree {size : Nat} {input selected : List Edge} {root : Int}
    {visited : Int → Prop} (state : TreeState input root visited selected)
    (nonempty : 0 < size) (valid : ValidInput size input) (connected : ConnectedOn size input)
    (covered : ∀ vertex : Int, 0 ≤ vertex → vertex < size → visited vertex) :
    MinimumSpanningTree size input selected := by
  apply MinimumSpanningForest.tree (state.minimum_spanning_forest ?_) nonempty valid connected
  intro edge member
  exact ⟨covered edge.source (valid.source edge member).1 (valid.source edge member).2,
    covered edge.target (valid.target edge member).1 (valid.target edge member).2⟩









theorem Frontier.initial (visited : Int → Prop) (key : Int → Int) :
    Frontier (fun _ => False) visited key (fun _ => -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    omega
  · intro edge impossible
    exact False.elim impossible
  · intro edge impossible
    exact False.elim impossible

/-- Removing a vertex from the queue preserves every remaining key invariant. -/
theorem Frontier.grow_visited {processed : Edge → Prop} {before after : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed before key parent)
    (grows : ∀ vertex, before vertex → after vertex) : Frontier processed after key parent := by
  have outside {vertex} (h : ¬ after vertex) : ¬ before vertex := fun old => h (grows vertex old)
  exact ⟨fun vertex h => frontier.witness vertex (outside h),
    fun edge member h => frontier.complete edge member (outside h),
    fun edge member h => frontier.least edge member (outside h)⟩

/-- An edge to an already selected vertex does not affect the frontier. -/
theorem Frontier.add_visited {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed visited key parent)
    (edge : Edge) (inside : visited edge.target) :
    Frontier (fun candidate => candidate = edge ∨ processed candidate) visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨candidate, member, source, target, cost⟩ := frontier.witness vertex outside known
    exact ⟨candidate, Or.inr member, source, target, cost⟩
  · intro candidate member outside
    rcases member with rfl | member
    · exact False.elim (outside inside)
    · exact frontier.complete candidate member outside
  · intro candidate member outside
    rcases member with rfl | member
    · exact False.elim (outside inside)
    · exact frontier.least candidate member outside

/-- An equally expensive or heavier edge leaves a known key and its parent unchanged. -/
theorem Frontier.add_keep {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed visited key parent)
    (edge : Edge) (known : 0 ≤ parent edge.target) (expensive : key edge.target ≤ edge.weight) :
    Frontier (fun candidate => candidate = edge ∨ processed candidate) visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside present
    obtain ⟨candidate, member, source, target, cost⟩ := frontier.witness vertex outside present
    exact ⟨candidate, Or.inr member, source, target, cost⟩
  · intro candidate member outside
    rcases member with rfl | member
    · exact known
    · exact frontier.complete candidate member outside
  · intro candidate member outside
    rcases member with rfl | member
    · exact expensive
    · exact frontier.least candidate member outside

/-- A newly discovered or cheaper edge replaces exactly its target's key and
parent. This local lemma matches the two assignments in Prim's relaxation branch. -/
theorem Frontier.add_improve {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier processed visited key parent)
    (edge : Edge) (sourceNonnegative : 0 ≤ edge.source)
    (better : parent edge.target < 0 ∨ edge.weight ≤ key edge.target) :
    Frontier (fun candidate => candidate = edge ∨ processed candidate) visited
      (assign key edge.target edge.weight) (assign parent edge.target edge.source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    by_cases same : vertex = edge.target
    · subst vertex
      exact ⟨edge, Or.inl rfl, by simp [assign], rfl, by simp [assign]⟩
    · simp only [assign, same, ↓reduceIte] at known ⊢
      obtain ⟨candidate, member, source, target, cost⟩ := frontier.witness vertex outside known
      exact ⟨candidate, Or.inr member, source, target, cost⟩
  · intro candidate member outside
    by_cases same : candidate.target = edge.target
    · simpa [assign, same] using sourceNonnegative
    · simp only [assign, same, ↓reduceIte]
      rcases member with rfl | member
      · exact False.elim (same rfl)
      · exact frontier.complete candidate member outside
  · intro candidate member outside
    by_cases same : candidate.target = edge.target
    · simp only [assign, same, ↓reduceIte]
      rcases member with rfl | member
      · exact Int.le_refl _
      · have bound := frontier.least candidate member outside
        have known := frontier.complete candidate member outside
        rw [same] at bound known
        rcases better with absent | cheaper
        · omega
        · exact Int.le_trans cheaper bound
    · simp only [assign, same, ↓reduceIte]
      rcases member with rfl | member
      · exact False.elim (same rfl)
      · exact frontier.least candidate member outside

/-- Equivalent descriptions of processed edges give the same frontier invariant. -/
theorem Frontier.congr_processed {before after : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} (frontier : Frontier before visited key parent)
    (same : ∀ edge, before edge ↔ after edge) : Frontier after visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨edge, member, source, target, cost⟩ := frontier.witness vertex outside known
    exact ⟨edge, (same edge).mp member, source, target, cost⟩
  · intro edge member outside
    exact frontier.complete edge ((same edge).mpr member) outside
  · intro edge member outside
    exact frontier.least edge ((same edge).mpr member) outside







/-- A queue that stores the discovered unvisited vertices extracts a light edge.
The queue's minimum requirement ranges only over discovered vertices, so no
artificial infinity value is needed for undiscovered keys. -/
theorem Keys.extract {input : List Edge} {visited : Int → Prop} {key parent : Int → Int}
    (keys : Keys input visited key parent) (symmetric : Symmetric input)
    (vertex : Int) (outside : ¬ visited vertex) (known : 0 ≤ parent vertex)
    (least : ∀ other, ¬ visited other → 0 ≤ parent other → key vertex ≤ key other) :
    ∃ edge, LightEdge input visited edge ∧ edge.source = parent vertex ∧
      edge.target = vertex ∧ edge.weight = key vertex ∧ visited edge.source := by
  obtain ⟨edge, ⟨member, sourceInside⟩, source, target, cost⟩ := keys.witness vertex outside known
  refine ⟨edge, ⟨member, Or.inl ⟨sourceInside, target ▸ outside⟩, ?_⟩,
    source, target, cost, sourceInside⟩
  intro candidate candidateMember crossing
  rw [cost]
  rcases crossing with forward | backward
  · exact Int.le_trans (least candidate.target forward.2
      (keys.complete candidate ⟨candidateMember, forward.1⟩ forward.2))
      (keys.least candidate ⟨candidateMember, forward.1⟩ forward.2)
  · obtain ⟨reverse, reverseMember, reverseSource, reverseTarget, reverseCost⟩ :=
      symmetric candidate candidateMember
    have inside : visited reverse.source := reverseSource ▸ backward.1
    have unvisited : ¬ visited reverse.target := reverseTarget ▸ backward.2
    have bound := Int.le_trans (least reverse.target unvisited
      (keys.complete reverse ⟨reverseMember, inside⟩ unvisited))
      (keys.least reverse ⟨reverseMember, inside⟩ unvisited)
    simpa [reverseCost] using bound

/-- An empty frontier has already reached every vertex connected to its visited root. -/
theorem Keys.reachable_of_empty {input : List Edge} {visited : Int → Prop}
    {key parent : Int → Int} (keys : Keys input visited key parent)
    (symmetric : Symmetric input) {root vertex : Int} (rootInside : visited root)
    (path : Connected input root vertex)
    (empty : ∀ other, ¬ visited other → parent other < 0) : visited vertex := by
  classical
  apply Classical.byContradiction
  intro outside
  obtain ⟨edge, member, crossing⟩ := path.crosses_cut visited rootInside outside
  rcases crossing with forward | backward
  · have known := keys.complete edge ⟨member, forward.1⟩ forward.2
    have absent := empty edge.target forward.2
    omega
  · obtain ⟨reverse, reverseMember, source, target, cost⟩ := symmetric edge member
    have inside : visited reverse.source := source ▸ backward.1
    have unvisited : ¬ visited reverse.target := target ▸ backward.2
    have known := keys.complete reverse ⟨reverseMember, inside⟩ unvisited
    have absent := empty reverse.target unvisited
    omega



theorem KeyScan.append {visited : Int → Prop} {source : Int} {first second : List (Int × Int)}
    {key parent middleKey middleParent finalKey finalParent : Int → Int}
    (one : KeyScan visited source first key parent middleKey middleParent)
    (two : KeyScan visited source second middleKey middleParent finalKey finalParent) :
    KeyScan visited source (first ++ second) key parent finalKey finalParent := by
  induction one with
  | done => exact two
  | skip inside rest ih => exact .skip inside (ih two)
  | keep outside known expensive rest ih => exact .keep outside known expensive (ih two)
  | improve outside better rest ih => exact .improve outside better (ih two)

/-- Scanning never changes the key or parent of an already visited vertex. -/
theorem KeyScan.visited_unchanged {visited : Int → Prop} {source : Int} {edges : List (Int × Int)}
    {key parent finalKey finalParent : Int → Int}
    (scan : KeyScan visited source edges key parent finalKey finalParent)
    (vertex : Int) (inside : visited vertex) :
    finalKey vertex = key vertex ∧ finalParent vertex = parent vertex := by
  induction scan with
  | done => exact ⟨rfl, rfl⟩
  | skip _ _ ih => exact ih
  | keep _ _ _ _ ih => exact ih
  | @improve other cost rest key parent finalKey finalParent outside better scan ih =>
    have different : vertex ≠ other := fun same => outside (same ▸ inside)
    simpa [assign, different] using ih

/-- Edge identity does not affect a relaxation: parallel occurrences with the
same endpoints and weight provide the same frontier guarantees. -/
theorem Frontier.add_payload {processed : Edge → Prop} {visited : Int → Prop}
    {key parent : Int → Int} {edge : Edge} {input : List Edge}
    (frontier : Frontier (fun candidate => candidate = edge ∨ processed candidate)
      visited key parent) (member : edge ∈ input) :
    Frontier (fun candidate => processed candidate ∨
      candidate ∈ input ∧ candidate.source = edge.source ∧
        candidate.target = edge.target ∧ candidate.weight = edge.weight) visited key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨candidate, candidateMember, source, target, cost⟩ := frontier.witness vertex outside known
    refine ⟨candidate, ?_, source, target, cost⟩
    rcases candidateMember with rfl | old
    · exact Or.inr ⟨member, rfl, rfl, rfl⟩
    · exact Or.inl old
  · intro candidate candidateMember outside
    rcases candidateMember with old | ⟨_, _, target, _⟩
    · exact frontier.complete candidate (Or.inr old) outside
    · rw [target] at outside ⊢
      exact frontier.complete edge (Or.inl rfl) outside
  · intro candidate candidateMember outside
    rcases candidateMember with old | ⟨_, _, target, cost⟩
    · exact frontier.least candidate (Or.inr old) outside
    · rw [target] at outside ⊢
      rw [cost]
      exact frontier.least edge (Or.inl rfl) outside

/-- A completed adjacency scan incorporates all of that list's edge occurrences
into the frontier, while retaining every earlier scanned edge. -/
theorem KeyScan.frontier {visited : Int → Prop} {source : Int} {edges : List (Int × Int)}
    {key parent finalKey finalParent : Int → Int}
    (scan : KeyScan visited source edges key parent finalKey finalParent)
    (input : List Edge) (sourceNonnegative : 0 ≤ source)
    (members : ∀ pair ∈ edges, ∃ edge ∈ input,
      edge.source = source ∧ edge.target = pair.1 ∧ edge.weight = pair.2)
    {processed : Edge → Prop} (frontier : Frontier processed visited key parent) :
    Frontier (fun edge => processed edge ∨ edge ∈ input ∧ edge.source = source ∧
      (edge.target, edge.weight) ∈ edges) visited finalKey finalParent := by
  induction scan generalizing processed with
  | done key parent =>
    exact frontier.congr_processed (by simp)
  | @skip vertex cost rest key parent finalKey finalParent inside scan ih =>
    obtain ⟨edge, member, sourceEq, targetEq, weightEq⟩ := members (vertex, cost) (by simp)
    have next := (frontier.add_visited edge (targetEq ▸ inside)).add_payload member
    have result := ih (fun pair present => members pair (by simp [present])) next
    apply result.congr_processed
    intro candidate
    simp only [sourceEq, targetEq, weightEq, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((old | ⟨inInput, source, target, cost⟩) | ⟨inInput, source, tail⟩)
      · exact Or.inl old
      · exact Or.inr ⟨inInput, source, Or.inl ⟨target, cost⟩⟩
      · exact Or.inr ⟨inInput, source, Or.inr tail⟩
    · rintro (old | ⟨inInput, source, (⟨target, cost⟩ | tail)⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨inInput, source, target, cost⟩)
      · exact Or.inr ⟨inInput, source, tail⟩
  | @keep vertex cost rest key parent finalKey finalParent outside known expensive scan ih =>
    obtain ⟨edge, member, sourceEq, targetEq, weightEq⟩ := members (vertex, cost) (by simp)
    have next := (frontier.add_keep edge (targetEq ▸ known)
      (by simpa [targetEq, weightEq] using expensive)).add_payload member
    have result := ih (fun pair present => members pair (by simp [present])) next
    apply result.congr_processed
    intro candidate
    simp only [sourceEq, targetEq, weightEq, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((old | ⟨inInput, source, target, cost⟩) | ⟨inInput, source, tail⟩)
      · exact Or.inl old
      · exact Or.inr ⟨inInput, source, Or.inl ⟨target, cost⟩⟩
      · exact Or.inr ⟨inInput, source, Or.inr tail⟩
    · rintro (old | ⟨inInput, source, (⟨target, cost⟩ | tail)⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨inInput, source, target, cost⟩)
      · exact Or.inr ⟨inInput, source, tail⟩
  | @improve vertex cost rest key parent finalKey finalParent outside better scan ih =>
    obtain ⟨edge, member, sourceEq, targetEq, weightEq⟩ := members (vertex, cost) (by simp)
    have sourceValid : 0 ≤ edge.source := by simpa [sourceEq] using sourceNonnegative
    have betterEdge : parent edge.target < 0 ∨ edge.weight ≤ key edge.target := by
      rw [targetEq, weightEq]
      rcases better with absent | cheaper
      · exact Or.inl absent
      · exact Or.inr (Int.le_of_lt cheaper)
    have next := (frontier.add_improve edge sourceValid betterEdge).add_payload member
    rw [targetEq, weightEq, sourceEq] at next
    have result := ih (fun pair present => members pair (by simp [present])) next
    apply result.congr_processed
    intro candidate
    simp only [List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((old | ⟨inInput, source, target, cost⟩) | ⟨inInput, source, tail⟩)
      · exact Or.inl old
      · exact Or.inr ⟨inInput, source, Or.inl ⟨target, cost⟩⟩
      · exact Or.inr ⟨inInput, source, Or.inr tail⟩
    · rintro (old | ⟨inInput, source, (⟨target, cost⟩ | tail)⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨inInput, source, target, cost⟩)
      · exact Or.inr ⟨inInput, source, tail⟩

/-- Before selecting the root, every vertex is undiscovered and no key is constrained. -/
theorem Keys.initial (input : List Edge) (key : Int → Int) :
    Keys input (fun _ => False) key (fun _ => -1) :=
  (Frontier.initial (fun _ => False) key).congr_processed (by simp)

/-- One complete main-loop iteration extends the visited set by its extracted
vertex and scans exactly that vertex's adjacency list. All resulting keys again
describe the full boundary of the enlarged tree. -/
theorem KeyScan.keys_after_selection {input : List Edge} {visited : Int → Prop}
    {source : Int} {edges : List (Int × Int)} {key parent finalKey finalParent : Int → Int}
    (keys : Keys input visited key parent)
    (scan : KeyScan (fun vertex => visited vertex ∨ vertex = source) source
      edges key parent finalKey finalParent)
    (sourceNonnegative : 0 ≤ source)
    (members : ∀ pair ∈ edges, ∃ edge ∈ input,
      edge.source = source ∧ edge.target = pair.1 ∧ edge.weight = pair.2)
    (complete : ∀ edge ∈ input, edge.source = source → (edge.target, edge.weight) ∈ edges) :
    Keys input (fun vertex => visited vertex ∨ vertex = source) finalKey finalParent := by
  have next := keys.grow_visited (after := fun vertex => visited vertex ∨ vertex = source)
    (fun _ old => Or.inl old)
  have scanned := scan.frontier input sourceNonnegative members next
  apply scanned.congr_processed
  intro edge
  constructor
  · rintro (⟨member, old⟩ | ⟨member, source, _⟩)
    · exact ⟨member, Or.inl old⟩
    · exact ⟨member, Or.inr source⟩
  · rintro ⟨member, old | source⟩
    · exact Or.inl ⟨member, old⟩
    · exact Or.inr ⟨member, source, complete edge member source⟩

/-- Replacing the representation of the visited predicate preserves all key facts. -/
theorem Keys.congr_visited {input : List Edge} {before after : Int → Prop}
    {key parent : Int → Int} (keys : Keys input before key parent)
    (same : ∀ vertex, before vertex ↔ after vertex) : Keys input after key parent := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex outside known
    obtain ⟨edge, ⟨member, inside⟩, source, target, cost⟩ :=
      keys.witness vertex (fun old => outside ((same vertex).mp old)) known
    exact ⟨edge, ⟨member, (same edge.source).mp inside⟩, source, target, cost⟩
  · intro edge member outside
    exact keys.complete edge ⟨member.1, (same edge.source).mpr member.2⟩
      (fun old => outside ((same edge.target).mp old))
  · intro edge member outside
    exact keys.least edge ⟨member.1, (same edge.source).mpr member.2⟩
      (fun old => outside ((same edge.target).mp old))

end Algo2Lean.Prim

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Prim's whole-loop invariant and its parent-sequence output specification.
The proof separates the first root extraction from ordinary light-edge choices,
then reuses the cut theorem and adjacency-scan lemmas at every iteration.
-/

namespace Algo2Lean.Prim

open Algo2Lean.Kruskal





theorem Invariant.initial (input : List Edge) (root : Int) (key : Int → Int) :
    Invariant input root (fun _ => False) key (fun _ => -1) [] := by
  refine ⟨Keys.initial input key, Or.inl ⟨by simp, rfl, by simp⟩, rfl, by simp, ?_⟩
  simp

/-- The root is either already selected or is the vertex selected by this first
iteration. The adjacency scan therefore always preserves the root's parent. -/
theorem Invariant.root_after_selection {input : List Edge} {root : Int} {visited : Int → Prop}
    {key parent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root visited key parent chosen) (vertex : Int)
    (root_or_known : vertex = root ∨ 0 ≤ parent vertex) : visited root ∨ root = vertex := by
  rcases invariant.tree with ⟨_, _, undiscovered⟩ | tree
  · rcases root_or_known with same | known
    · exact Or.inr same.symm
    · rw [undiscovered vertex] at known
      omega
  · exact Or.inl tree.root_visited

/-- An iteration selects one new vertex and scans its whole adjacency list.
The extracted key need only be minimum among discovered unvisited vertices. -/
theorem Invariant.iteration {input : List Edge} {root : Int} {visited : Int → Prop}
    {key parent finalKey finalParent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root visited key parent chosen) (symmetric : Symmetric input)
    (vertex : Int) (outside : ¬ visited vertex) (nonnegative : 0 ≤ vertex)
    (root_or_known : vertex = root ∨ 0 ≤ parent vertex)
    (least : ∀ other, ¬ visited other → 0 ≤ parent other → key vertex ≤ key other)
    (edges : List (Int × Int))
    (scan : KeyScan (fun value => visited value ∨ value = vertex) vertex
      edges key parent finalKey finalParent)
    (members : ∀ pair ∈ edges, ∃ edge ∈ input,
      edge.source = vertex ∧ edge.target = pair.1 ∧ edge.weight = pair.2)
    (complete : ∀ edge ∈ input, edge.source = vertex → (edge.target, edge.weight) ∈ edges) :
    ∃ nextChosen, Invariant input root (fun value => visited value ∨ value = vertex)
      finalKey finalParent nextChosen := by
  have keys := scan.keys_after_selection invariant.keys nonnegative members complete
  rcases invariant.tree with ⟨empty, chosenEmpty, undiscovered⟩ | tree
  · have isRoot : vertex = root := by
      rcases root_or_known with same | known
      · exact same
      · rw [undiscovered vertex] at known
        omega
    have nextTree : TreeState input root (fun value => visited value ∨ value = vertex) [] := by
      apply (TreeState.initial input root).congr_visited
      intro value
      constructor
      · intro same
        exact Or.inr (same.trans isRoot.symm)
      · rintro (old | same)
        · exact False.elim (empty value old)
        · exact same.trans isRoot
    refine ⟨[], keys, Or.inr nextTree, ?_, by simp, ?_⟩
    · exact (scan.visited_unchanged root (Or.inr isRoot.symm)).2.trans invariant.root_parent
    · intro value
      simp only [List.not_mem_nil, false_and, exists_false, iff_false]
      rintro ⟨old | same, notRoot⟩
      · exact empty value old
      · exact notRoot (same.trans isRoot)
  · have notRoot : vertex ≠ root := by
      intro same
      exact outside (same ▸ tree.root_visited)
    have known : 0 ≤ parent vertex := root_or_known.resolve_left notRoot
    obtain ⟨edge, light, source, target, cost, sourceInside⟩ :=
      invariant.keys.extract symmetric vertex outside known least
    have nextTree := tree.extend light sourceInside (target ▸ outside)
    rw [target] at nextTree
    refine ⟨edge :: chosen, keys, Or.inr nextTree, ?_, ?_, ?_⟩
    · exact (scan.visited_unchanged root (Or.inl tree.root_visited)).2.trans invariant.root_parent
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · rw [target]
        exact ⟨(scan.visited_unchanged vertex (Or.inr rfl)).2.trans source.symm, notRoot⟩
      · obtain ⟨parentEq, targetNotRoot⟩ := invariant.parents candidate member
        exact ⟨(scan.visited_unchanged candidate.target
          (Or.inl (tree.endpoints candidate member).2)).2.trans parentEq, targetNotRoot⟩
    · intro value
      constructor
      · rintro ⟨old | same, valueNotRoot⟩
        · obtain ⟨candidate, member, targetEq⟩ := (invariant.targets value).mp ⟨old, valueNotRoot⟩
          exact ⟨candidate, List.mem_cons_of_mem edge member, targetEq⟩
        · exact ⟨edge, by simp, target.trans same.symm⟩
      · rintro ⟨candidate, member, targetEq⟩
        rcases List.mem_cons.mp member with rfl | member
        · have same : value = vertex := targetEq.symm.trans target
          exact ⟨Or.inr same, fun rootEq => notRoot (same.symm.trans rootEq)⟩
        · have old := (invariant.targets value).mpr ⟨candidate, member, targetEq⟩
          exact ⟨Or.inl old.1, old.2⟩

/-- Equivalent visited predicates may be substituted without changing keys,
chosen edges, or the output parent representation. -/
theorem Invariant.congr_visited {input : List Edge} {root : Int} {before after : Int → Prop}
    {key parent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root before key parent chosen)
    (same : ∀ vertex, before vertex ↔ after vertex) :
    Invariant input root after key parent chosen := by
  refine ⟨invariant.keys.congr_visited same, ?_, invariant.root_parent, invariant.parents, ?_⟩
  · rcases invariant.tree with ⟨empty, chosenEmpty, undiscovered⟩ | tree
    · exact Or.inl ⟨fun vertex present => empty vertex ((same vertex).mpr present),
        chosenEmpty, undiscovered⟩
    · exact Or.inr (tree.congr_visited same)
  · intro vertex
    rw [← same vertex]
    exact invariant.targets vertex

-- Main result: Correctness
/-- When the queue is empty on a connected finite graph, Prim's final parent
sequence describes a minimum spanning tree. This conclusion compares its weight
with every spanning forest; no nonnegativity of edge weights is assumed. -/
theorem Invariant.finish {size : Nat} {input : List Edge} {root : Int} {visited : Int → Prop}
    {key parent : Int → Int} {chosen : List Edge}
    (invariant : Invariant input root visited key parent chosen)
    (symmetric : Symmetric input) (valid : ValidInput size input) (connected : ConnectedOn size input)
    (rootNonnegative : 0 ≤ root) (rootBelow : root < size) (rootInside : visited root)
    (empty : ∀ vertex, ¬ visited vertex → parent vertex < 0) :
    SpanningParents size input root parent := by
  have nonempty : 0 < size := by omega
  have covered : ∀ vertex : Int, 0 ≤ vertex → vertex < size → visited vertex := by
    intro vertex lower upper
    have path : Connected input root vertex := by
      have naturalPath := connected root.toNat vertex.toNat (Nat.zero_le _) (by omega)
        (Nat.zero_le _) (by omega)
      have rootCast : (root.toNat : Int) = root := by omega
      have vertexCast : (vertex.toNat : Int) = vertex := by omega
      simpa only [rootCast, vertexCast] using naturalPath
    exact invariant.keys.reachable_of_empty symmetric rootInside
      path empty
  have tree : TreeState input root visited chosen := by
    rcases invariant.tree with ⟨none, _, _⟩ | tree
    · exact False.elim (none root rootInside)
    · exact tree
  refine ⟨chosen, tree.minimum_spanning_tree nonempty valid connected covered,
    invariant.root_parent, invariant.parents, ?_⟩
  intro vertex lower upper notRoot
  exact (invariant.targets vertex).mp ⟨covered vertex lower upper, notRoot⟩

end Algo2Lean.Prim

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Queue storage and compositional clock accounting for Prim. The queue backend
is abstract, and its amortized potential is carried through actual calls. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl
variable (dependencies : Dependencies)







variable {dependencies}
variable {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)



namespace QueueState






end QueueState



theorem Storage.tick {state : QueueState model} (storage : Storage model state) (name : String) :
    Storage model (state.tick model name) :=
  ⟨storage.graph.preserved (graph_frame_tick _ _ _ name 1),
    model.tick storage.queue name 1, storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated,storage.keyParent,storage.parentSelected,storage.separate⟩

theorem Storage.write {state : QueueState model} (storage : Storage model state)
    (ref : SeqRef) (index value : Int) (member : ref ∈ client.protection.sequences) :
    Storage model (state.write model ref index value) :=
  ⟨storage.graph.preserved (graph_frame_write _ _ _ ref index value),
    model.write storage.queue ref member index value,
    storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated,storage.keyParent,storage.parentSelected,storage.separate⟩

/-- The generic queue frame implies preservation of the imported graph. -/
theorem graph_frame_of_protected {before after : Heap}
    (representation : GraphRep before client.graph client.size client.heads client.adjacency)
    (frame : PriorityQueueAnalysis.Frame client.protection before after) :
    GraphFrame before after client.graph client.heads := by
  have validGraph : is_Graph after client.graph :=
    ⟨Nat.lt_of_lt_of_le representation.valid.1 frame.nextObject,
      (frame.classes _ representation.valid.1).trans representation.valid.2⟩
  have graphFields : after.objects client.graph = before.objects client.graph :=
    frame.objects _ "prim.graph.Graph" representation.valid.1 representation.valid.2 (by simp [Client.protection])
  have graphRead : ∀ field, after.readField client.graph field = before.readField client.graph field := by
    intro field
    simp [Heap.readField,graphFields]
  have oldHeads : client.heads < before.nextCollection := representation.headsValid.1
  have headsType : after.sequenceType client.heads = before.sequenceType client.heads := frame.types _ oldHeads
  have headsValid : seq_Edge_optional.valid after client.heads :=
    ⟨Nat.lt_of_lt_of_le oldHeads frame.nextCollection, headsType.trans representation.headsValid.2⟩
  have collections := frame.collections _ (by simp [Client.protection]) oldHeads
  have entries : ∀ vertex, seq_Edge_optional.get after client.heads vertex =
      seq_Edge_optional.get before client.heads vertex := by
    intro vertex
    simp [SequenceType.get,headsValid,representation.headsValid,Heap.readElement,collections]
  refine ⟨fun _ => validGraph, ?_, ?_, fun _ => headsValid, entries, ?_⟩
  · simp [field_Graph_size, validGraph,representation.valid,graphRead]
  · simp [field_Graph_heads, validGraph,representation.valid,graphRead]
  · intro ref valid
    have newValid : is_Edge after ref :=
      ⟨Nat.lt_of_lt_of_le valid.1 frame.nextObject, (frame.classes _ valid.1).trans valid.2⟩
    have fields := frame.objects ref "prim.graph.Edge" valid.1 valid.2 (by simp [Client.protection])
    have reads : ∀ field, after.readField ref field = before.readField ref field := by
      intro field
      simp [Heap.readField,fields]
    exact ⟨newValid, by simp [field_Edge_target,valid,newValid,reads],
      by simp [field_Edge_weight,valid,newValid,reads],
      by simp [field_Edge_next,valid,newValid,reads]⟩

theorem Storage.preserved {before after : QueueState model} (storage : Storage model before)
    (rep : model.Rep after.heap after.queueState)
    (frame : PriorityQueueAnalysis.Frame client.protection before.heap after.heap) :
    Storage model after :=
  ⟨storage.graph.preserved (graph_frame_of_protected storage.graph frame),rep,
    Nat.lt_of_lt_of_le storage.keyAllocated frame.nextRef,
    Nat.lt_of_lt_of_le storage.parentAllocated frame.nextRef,
    Nat.lt_of_lt_of_le storage.selectedAllocated frame.nextRef,storage.keyParent,storage.parentSelected,storage.separate⟩





theorem work_triangle (a b c : Heap) : work model a c ≤ work model a b + work model b c := by
  rw [work,work,work,← Clocks.weighted_add]
  apply Clocks.weighted_le
  intro name
  simp only [Heap.cost,Clocks.add]
  omega



theorem CostBounds.refl (state : QueueState model) : CostBounds model state state 0 0 := by
  have zero : Heap.cost state.heap state.heap = (fun _ => 0) := by
    funext name
    simp [Heap.cost]
  constructor <;> simp [zero,work]

theorem CostBounds.trans {a b c : QueueState model} {v e v' e' : Nat}
    (one : CostBounds model a b v e) (two : CostBounds model b c v' e') :
    CostBounds model a c (v+v') (e+e') := by
  have cost (name : String) : Heap.cost a.heap c.heap name ≤
      Heap.cost a.heap b.heap name + Heap.cost b.heap c.heap name := by
    simp only [Heap.cost]
    omega
  refine ⟨Nat.le_trans (cost _) (Nat.add_le_add one.updates two.updates),
    Nat.le_trans (cost _) (Nat.add_le_add one.pops two.pops),
    Nat.le_trans (cost _) (Nat.add_le_add one.checks two.checks),
    Nat.le_trans (cost _) (Nat.add_le_add one.visits two.visits),
    Nat.le_trans (cost _) (Nat.add_le_add one.improvements two.improvements),
    Nat.le_trans (cost _) (Nat.add_le_add one.settlements two.settlements), ?_⟩
  have triangle := work_triangle model a.heap b.heap c.heap
  have first := one.amortized
  have second := two.amortized
  simp only [Nat.mul_add]
  omega

theorem CostBounds.weaken {a b : QueueState model} {v e v' e' : Nat}
    (one : CostBounds model a b v e) (vertices : v ≤ v') (edges : e ≤ e') :
    CostBounds model a b v' e' := by
  refine ⟨Nat.le_trans one.updates edges,Nat.le_trans one.pops vertices,Nat.le_trans one.checks vertices,
    Nat.le_trans one.visits edges,Nat.le_trans one.improvements edges,Nat.le_trans one.settlements vertices,?_⟩
  exact Nat.le_trans one.amortized (Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ edges) _)
    (Nat.mul_le_mul_left _ vertices))

variable (contracts : Contracts model reservedClocks)
include contracts

theorem work_tick_left (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model (before.tick name) after = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]

theorem work_tick_right (before after : Heap) (name : String) (reserved : name ∈ reservedClocks) :
    work model before (after.tick name) = work model before after := by
  unfold work Clocks.weighted
  congr 1
  apply List.map_congr_left
  intro item member
  simp [Heap.cost,Heap.tick,contracts.metricReserved name reserved item member]





theorem queue_update (state : QueueState model) (vertex key : Int) (storage : Storage model state)
    (lower : 0 ≤ vertex) (upper : vertex < model.capacity)
    (improves : ∀ old, (vertex,old) ∈ state.entries model → key < old) :
    ∃ after, QueueUpdated model state after vertex key := by
  obtain ⟨heap,next,effect⟩ := contracts.update state.heap state.queueState vertex key storage.queue lower upper improves
  exact ⟨⟨heap,next⟩,effect.execution,storage.preserved model effect.represented effect.frame,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.keyAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.parentAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.selectedAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩

theorem queue_extract (state : QueueState model) (storage : Storage model state)
    (nonempty : state.entries model ≠ []) : ∃ after vertex key, QueueExtracted model state after vertex key := by
  obtain ⟨heap,next,vertex,key,effect⟩ := contracts.extract state.heap state.queueState storage.queue nonempty
  exact ⟨⟨heap,next⟩,vertex,key,effect.execution,storage.preserved model effect.represented effect.frame,
    effect.selected,effect.least,effect.contents,
    effect.frame.sequences _ (by simp [Client.protection]) storage.keyAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.parentAllocated,
    effect.frame.sequences _ (by simp [Client.protection]) storage.selectedAllocated,
    graph_frame_of_protected storage.graph effect.frame,effect.clocks,effect.amortized⟩

theorem skip_edge_cost (state : QueueState model) :
    CostBounds model state (state.tick model "edges") 0 1 := by
  have zero : work model state.heap state.heap = 0 := Heap.weightedCost_self _ _
  constructor <;> try simp [QueueState.tick,Heap.cost,Heap.tick]
  change work model state.heap (state.heap.tick "edges") + _ ≤ _
  rw [work_tick_right model contracts _ _ "edges" (by simp [reservedClocks]),zero]
  simp

theorem updated_edge_cost {state after : QueueState model} {vertex target candidate : Int}
    (effect : QueueUpdated model
      ((((state.tick model "edges").write model client.key target candidate).write model client.parent target vertex).tick model "queue_updates")
      after target candidate) :
    CostBounds model state (after.tick model "improvements") 0 1 := by
  have clocks (name) (member : name ∈ reservedClocks) := effect.bookkeeping name member
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have same := clocks "queue_updates" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_pops" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_empty_checks" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "edges" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "improvements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "settlements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have bound := effect.amortized
    change work model ((((state.heap.tick "edges").write client.key target candidate).write client.parent target vertex).tick "queue_updates")
      after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "queue_updates" (by simp [reservedClocks])] at bound
    change work model (state.heap.tick "edges") after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "edges" (by simp [reservedClocks])] at bound
    change work model state.heap (after.heap.tick "improvements") + _ ≤ _
    rw [work_tick_right model contracts _ _ "improvements" (by simp [reservedClocks])]
    simpa [QueueState.tick,QueueState.write] using bound

theorem extracted_selected_cost {state after : QueueState model} {vertex key : Int}
    (effect : QueueExtracted model ((state.tick model "queue_empty_checks").tick model "queue_pops")
      after vertex key) :
    CostBounds model state ((after.write model client.selected vertex 1).tick model "settlements") 1 0 := by
  have clocks (name) (member : name ∈ reservedClocks) := effect.bookkeeping name member
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have same := clocks "queue_updates" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_pops" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "queue_empty_checks" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "edges" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "improvements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have same := clocks "settlements" (by simp [reservedClocks])
    simp [QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at same ⊢
    omega
  · have bound := effect.amortized
    change work model ((state.heap.tick "queue_empty_checks").tick "queue_pops") after.heap + _ ≤ _ at bound
    rw [work_tick_left model contracts _ _ "queue_pops" (by simp [reservedClocks]),
      work_tick_left model contracts _ _ "queue_empty_checks" (by simp [reservedClocks])] at bound
    change work model state.heap ((after.heap.write client.selected vertex 1).tick "settlements") + _ ≤ _
    rw [work_tick_right model contracts _ _ "settlements" (by simp [reservedClocks])]
    simpa [QueueState.tick,QueueState.write] using! bound


end PrimAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Prim's adjacency scan preserves queue contents, parent pointers, and keys.
Every queue update uses only the imported operation contract. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo2Lean.Prim
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl

variable {dependencies : Dependencies} {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)
variable (contracts : Contracts model reservedClocks)
include contracts





/-- One adjacency cell is skipped or updates exactly one queue entry and parent. -/
theorem advance_edge (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (vertex target weight : Int)
    (edge : Ref_Edge) (next : Option Ref_Edge)
    (storage : Storage model state) (matching : QueueMatches model state)
    (vertexLower : 0 ≤ vertex) (rootSelected : state.heap.read client.selected client.root ≠ 0)
    (validEdge : is_Edge state.heap edge)
    (readTarget : field_Edge_target state.heap edge = some target)
    (readWeight : field_Edge_weight state.heap edge = some weight)
    (readNext : field_Edge_next state.heap edge = some next)
    (targetLower : 0 ≤ target) (targetUpper : target < client.size) :
    ∃ after, EdgeAdvanced model state after vertex target weight edge next := by
  have inputs : scan_edges.ValidInput dependencies state.heap
      (client.queue,client.key,client.parent,client.selected,vertex,some edge) :=
    ⟨model.valid storage.queue,storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated,
      by
        intro ref member
        have same : edge = ref := by simpa using member
        simpa only [←same] using validEdge⟩
  by_cases unselected : state.heap.read client.selected target = 0
  · by_cases better : state.heap.read client.parent target < 0 ∨ weight < state.heap.read client.key target
    · let prepared := (((state.tick model "edges").write model client.key target weight).write model client.parent target vertex).tick model "queue_updates"
      have preparedStorage : Storage model prepared :=
        (((storage.tick model "edges").write model _ target weight (by simp [Client.protection])).write model _ target vertex (by simp [Client.protection])).tick model "queue_updates"
      obtain ⟨after, updated⟩ := queue_update model contracts prepared target weight preparedStorage targetLower
        (by omega) (by
          intro old member
          have entry := (matching target old).mp member
          have notRoot : target ≠ client.root := by intro same; subst target; exact rootSelected unselected
          rcases entry.2.1 with same | known
          · exact False.elim (notRoot same)
          · omega)
      have keyFinal : (after.tick model "improvements").heap.read client.key =
          assign (state.heap.read client.key) target weight := by
        rw [show (after.tick model "improvements").heap.read client.key = after.heap.read client.key from rfl, updated.key]
        funext v
        simp [prepared,QueueState.tick,QueueState.write,Heap.read,Heap.write,assign,storage.keyParent]
      have parentFinal : (after.tick model "improvements").heap.read client.parent =
          assign (state.heap.read client.parent) target vertex := by
        rw [show (after.tick model "improvements").heap.read client.parent = after.heap.read client.parent from rfl, updated.parent]
        funext v
        simp [prepared,QueueState.tick,QueueState.write,Heap.read,Heap.write,assign,Ne.symm storage.keyParent]
      have selectedFinal : (after.tick model "improvements").heap.read client.selected =
          state.heap.read client.selected := by
        rw [show (after.tick model "improvements").heap.read client.selected = after.heap.read client.selected from rfl, updated.selected]
        funext v
        simp [prepared,QueueState.tick,QueueState.write,Heap.read,Heap.write,Ne.symm storage.separate,Ne.symm storage.parentSelected]
      have frame : GraphFrame state.heap (after.tick model "improvements").heap client.graph client.heads :=
        ((((graph_frame_tick _ _ _ "edges" 1).trans
          (graph_frame_write _ _ _ client.key target weight)).trans
          (graph_frame_write _ _ _ client.parent target vertex)).trans
          (graph_frame_tick _ _ _ "queue_updates" 1)).trans
          (updated.frame.trans (graph_frame_tick _ _ _ "improvements" 1))
      refine ⟨after.tick model "improvements",updated.storage.tick model "improvements",?_,selectedFinal,?_,
        updated_edge_cost model contracts updated,frame,?_⟩
      · intro v k
        change (v,k) ∈ after.entries model ↔ _
        rw [updated.contents,keyFinal,parentFinal,selectedFinal]
        change (v = target ∧ k = weight) ∨ (v ≠ target ∧ (v,k) ∈ state.entries model) ↔ _
        rw [matching]
        by_cases same : v = target <;> simp [assign,same,unselected,vertexLower]
      · rw [keyFinal,parentFinal]
        exact KeyScan.improve (by simpa using unselected) better (.done _ _)
      · intro finalHeap tail
        exact scan_improved dependencies state.heap after.heap finalHeap client.queue client.key client.parent client.selected
          vertex target weight edge next inputs readTarget readWeight
          (((frame.edges edge validEdge).2.2.2).trans readNext) unselected better updated.execution tail
    · have known : 0 ≤ state.heap.read client.parent target := by omega
      have expensive : state.heap.read client.key target ≤ weight := by omega
      refine ⟨state.tick model "edges",storage.tick model "edges",matching,rfl,?_,
        skip_edge_cost model contracts state,graph_frame_tick _ _ _ "edges" 1,?_⟩
      · exact KeyScan.keep (by simpa using unselected) known expensive (.done _ _)
      · intro finalHeap tail
        exact scan_unimproved dependencies state.heap finalHeap client.queue client.key client.parent client.selected
          vertex target weight edge next inputs readTarget readWeight readNext unselected known expensive tail
  · refine ⟨state.tick model "edges",storage.tick model "edges",matching,rfl,
      KeyScan.skip unselected (.done _ _),skip_edge_cost model contracts state,graph_frame_tick _ _ _ "edges" 1,?_⟩
    intro finalHeap tail
    exact scan_selected dependencies state.heap finalHeap client.queue client.key client.parent client.selected
      vertex target edge next inputs readTarget readNext unselected tail

/-- Scanning a finite adjacency list composes its local updates and clock bounds. -/
theorem scan_adjacency (capacity : client.size ≤ model.capacity)
    (state : QueueState model) (vertex : Int) (head : Option Ref_Edge) (edges : List (Int × Int))
    (storage : Storage model state) (matching : QueueMatches model state)
    (vertexLower : 0 ≤ vertex) (rootSelected : state.heap.read client.selected client.root ≠ 0)
    (chain : AdjacencyChain state.heap client.size head edges) :
    ∃ after, AdjacencyScanned model state after vertex head edges := by
  induction edges generalizing state head with
  | nil =>
    have empty : head = none := by cases chain; rfl
    subst head
    exact ⟨state,storage,matching,rfl,KeyScan.done _ _,CostBounds.refl model state,GraphFrame.refl _ _ _,
      scan_empty dependencies state.heap client.queue client.key client.parent client.selected vertex⟩
  | cons pair rest ih =>
    cases chain with
    | cons edge target weight next tail valid readTarget readWeight readNext lower upper remaining =>
      obtain ⟨middle,advanced⟩ := advance_edge model contracts capacity state vertex target weight edge next
        storage matching vertexLower rootSelected valid readTarget readWeight readNext lower upper
      obtain ⟨after,scanned⟩ := ih middle next advanced.storage advanced.matching
        (by rw [advanced.selected]; exact rootSelected) (remaining.preserved advanced.frame.edges)
      refine ⟨after,scanned.storage,scanned.matching,scanned.selected.trans advanced.selected,?_,?_,
        advanced.frame.trans scanned.frame,advanced.execution after.heap scanned.execution⟩
      · have tailScan := scanned.scan
        rw [advanced.selected] at tailScan
        exact advanced.scan.append tailScan
      · simpa [Nat.add_comm] using advanced.costs.trans model scanned.costs

end PrimAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Prim's algorithm with an abstract mutable priority queue. The proof connects
local source transitions, the cut-property invariant, and amortized operation
contracts. The Fibonacci instantiation reuses this analysis unchanged. -/
namespace PrimAnalysis
open Algo2LeanCore Algo2LeanGenerated Algo2Lean.Dijkstra
open Algo2Lean.Prim
open Algo.prim.graph.Algo2LeanGenerated
open Algo.prim.prim Algo.dijkstra.priority_queue
open PriorityQueueAnalysis PrimGraph PrimControl



variable {dependencies : Dependencies} {client : Client}
variable (model : Model dependencies.PriorityQueue client.queue client.protection)





variable (contracts : Contracts model reservedClocks)
include contracts

/-- One queue extraction is followed by one verified adjacency scan. -/
theorem extraction_step (capacity : client.size ≤ model.capacity)
    (symmetric : PrimGraph.Symmetric client.size client.adjacency)
    (state : QueueState model) (remaining : List Int) (invariant : LoopInvariant model state remaining)
    (nonempty : state.entries model ≠ []) :
    ∃ after vertex, Iteration model state after remaining vertex := by
  have emptySummary := contracts.is_empty (state.heap.tick "queue_empty_checks") state.queueState
    (model.tick invariant.storage.queue "queue_empty_checks" 1)
  let prepared := (state.tick model "queue_empty_checks").tick model "queue_pops"
  have preparedStorage : Storage model prepared :=
    (invariant.storage.tick model "queue_empty_checks").tick model "queue_pops"
  obtain ⟨popped,vertex,key,extracted⟩ := queue_extract model contracts prepared preparedStorage nonempty
  have selected := (invariant.matching vertex key).mp extracted.member
  obtain ⟨lower,upper⟩ := model.bounded invariant.storage.queue vertex key extracted.member
  have inSize : vertex < client.size := by
    obtain ⟨chosen,math⟩ := invariant.mathematical
    rcases selected.2.1 with root | known
    · simpa [root] using invariant.rootRange.2
    · obtain ⟨edge,⟨inInput,_⟩,_,target,_⟩ := math.keys.witness vertex (by simpa using selected.1) known
      have bound := invariant.storage.graph.validInput.target edge inInput
      rw [target] at bound
      have nonnegative := invariant.storage.graph.sizeNonnegative
      omega
  have member : vertex ∈ remaining := (invariant.members vertex).mpr ⟨lower,inSize,selected.1⟩
  let marked := (popped.write model client.selected vertex 1).tick model "settlements"
  have stored : Storage model marked :=
    (extracted.storage.write model _ vertex 1 (by simp [Client.protection])).tick model "settlements"
  have keySame : marked.heap.read client.key = state.heap.read client.key := by
    change (popped.heap.write client.selected vertex 1).read client.key = _
    rw [show (popped.heap.write client.selected vertex 1).read client.key = popped.heap.read client.key by
      funext v
      exact Heap.read_write_other_ref _ _ _ _ _ _ invariant.storage.separate]
    exact extracted.key
  have parentSame : marked.heap.read client.parent = state.heap.read client.parent := by
    change (popped.heap.write client.selected vertex 1).read client.parent = _
    rw [show (popped.heap.write client.selected vertex 1).read client.parent = popped.heap.read client.parent by
      funext v
      exact Heap.read_write_other_ref _ _ _ _ _ _ invariant.storage.parentSelected]
    exact extracted.parent
  have selectedValues (v : Int) : marked.heap.read client.selected v =
      if v = vertex then 1 else state.heap.read client.selected v := by
    change (popped.heap.write client.selected vertex 1).read client.selected v = _
    simpa [Heap.read,Heap.write] using!
      congrArg (fun value => if v = vertex then 1 else value) (congrFun extracted.selected v)
  have matching : QueueMatches model marked := by
    intro v k
    change (v,k) ∈ popped.entries model ↔ _
    rw [extracted.contents]
    change v ≠ vertex ∧ (v,k) ∈ state.entries model ↔ _
    rw [invariant.matching,keySame,parentSame,selectedValues]
    by_cases same : v = vertex <;> simp [same]
  have selectedPredicate : (fun v => marked.heap.read client.selected v ≠ 0) =
      (fun v => state.heap.read client.selected v ≠ 0 ∨ v = vertex) := by
    funext v
    rw [selectedValues]
    apply propext
    by_cases same : v = vertex <;> simp [same]
  obtain ⟨chosen,mathematical⟩ := invariant.mathematical
  have rootNow : marked.heap.read client.selected client.root ≠ 0 := by
    change (fun v => marked.heap.read client.selected v ≠ 0) client.root
    rw [selectedPredicate]
    exact mathematical.root_after_selection vertex selected.2.1
  obtain ⟨head,readHead,chain⟩ := stored.graph.chains vertex lower inSize
  obtain ⟨after,scanned⟩ := scan_adjacency model contracts capacity marked vertex head
    (client.adjacency vertex) stored matching lower rootNow chain
  have scan := scanned.scan
  rw [keySame,parentSame,selectedPredicate] at scan
  have least : ∀ other, ¬ state.heap.read client.selected other ≠ 0 →
      0 ≤ state.heap.read client.parent other → state.heap.read client.key vertex ≤ state.heap.read client.key other := by
    intro other outside known
    have entry := (invariant.matching other (state.heap.read client.key other)).mpr
      ⟨by simpa using outside,Or.inr known,rfl⟩
    simpa [selected.2.2] using extracted.least other _ entry
  obtain ⟨nextChosen,nextMath⟩ := mathematical.iteration
    (invariant.storage.graph.inputEdges_reverse symmetric) vertex (by simpa using selected.1)
    lower selected.2.1 least (client.adjacency vertex) scan
    (by
      intro pair present
      obtain ⟨id,member⟩ := (inputEdges_member client.size client.adjacency vertex pair.1 pair.2).mpr ⟨lower,inSize,present⟩
      exact ⟨⟨id,vertex,pair.1,pair.2⟩,member,rfl,rfl,rfl⟩)
    (by
      intro edge member same
      have observation := inputEdges_observation member
      simpa [same] using observation.2.2)
  have next : LoopInvariant model after (remaining.erase vertex) := by
    refine ⟨scanned.storage,scanned.matching,invariant.rootRange,invariant.unique.erase vertex,?_,nextChosen,?_⟩
    · intro v
      rw [invariant.unique.mem_erase_iff,invariant.members,scanned.selected,selectedValues]
      by_cases same : v = vertex <;> simp [same]
    · apply nextMath.congr_visited
      intro v
      rw [scanned.selected]
      exact (Iff.of_eq (congrFun selectedPredicate v)).symm
  refine ⟨after,vertex,member,next,?_,?_⟩
  · simpa using (extracted_selected_cost model contracts extracted).trans model scanned.costs
  · intro finalHeap continuation
    exact extract_next dependencies state.heap popped.heap after.heap finalHeap
      client.graph client.queue client.key client.parent client.selected vertex client.heads head
      (by simpa only [List.isEmpty_eq_false_iff.mpr nonempty] using emptySummary)
      extracted.execution extracted.storage.selectedAllocated stored.graph.readHeads readHead
      scanned.execution continuation



theorem extraction_loop (capacity : client.size ≤ model.capacity)
    (symmetric : PrimGraph.Symmetric client.size client.adjacency)
    (state : QueueState model) (remaining : List Int) (invariant : LoopInvariant model state remaining) :
    ∃ after, Completed model state after remaining := by
  suffices all : ∀ count state remaining, remaining.length = count → LoopInvariant model state remaining →
      ∃ after, Completed model state after remaining by
    exact all remaining.length state remaining rfl invariant
  intro count
  induction count using Nat.strongRecOn with
  | ind count ih =>
    intro state remaining length invariant
    by_cases empty : state.entries model = []
    · have emptySummary := contracts.is_empty (state.heap.tick "queue_empty_checks") state.queueState
        (model.tick invariant.storage.queue "queue_empty_checks" 1)
      refine ⟨state,⟨remaining,invariant⟩,empty,(CostBounds.refl model state).weaken model (Nat.zero_le _) (Nat.zero_le _),?_⟩
      exact extract_empty dependencies state.heap client.graph client.queue client.key client.parent client.selected
        invariant.storage.parentAllocated (by simpa only [empty,List.isEmpty_nil] using emptySummary)
    · obtain ⟨after,vertex,iteration⟩ := extraction_step model contracts capacity symmetric state remaining invariant empty
      have decreases := remaining_length remaining vertex iteration.member
      have smaller : (remaining.erase vertex).length < count := by omega
      obtain ⟨final,completed⟩ := ih (remaining.erase vertex).length smaller after (remaining.erase vertex) rfl iteration.invariant
      have vertices : 1 + (remaining.erase vertex).length = remaining.length := by omega
      have edges : (client.adjacency vertex).length + edgeBudget client.adjacency (remaining.erase vertex) =
          edgeBudget client.adjacency remaining := by
        have accounting := edgeBudget_erase client.adjacency remaining vertex iteration.member
        omega
      refine ⟨final,completed.invariant,completed.empty,?_,iteration.execution _ completed.execution⟩
      simpa only [vertices,edges] using iteration.costs.trans model completed.costs



/-- The reusable generic contract proves termination, minimum spanning-tree
correctness, caller preservation, and cost increments from the same execution. -/
theorem prim_complete (capacity : client.size ≤ model.capacity)
    (before : QueueState model) (storage : Storage model before)
    (empty : before.entries model = [])
    (keys : before.heap.read client.key = fun _ => 0)
    (parents : before.heap.read client.parent = fun _ => -1)
    (flags : before.heap.read client.selected = fun _ => 0)
    (rootLower : 0 ≤ client.root) (rootUpper : client.root < client.size)
    (symmetric : PrimGraph.Symmetric client.size client.adjacency)
    (connected : Algo2Lean.Kruskal.ConnectedOn client.size.toNat (inputEdges client.size client.adjacency)) :
    ∃ after,
      prim.Call dependencies before.heap
        (client.graph,client.root,client.queue,client.key,client.parent,client.selected) after client.parent ∧
      GraphRep after client.graph client.size client.heads client.adjacency ∧
      MinimumSpanningParents client.size client.adjacency client.root (after.read client.parent) ∧
      OperationCounts before.heap after client.size.toNat (edgeBudget client.adjacency (vertexRange client.size)) ∧
      work model before.heap after ≤ before.potential model +
        model.updateBudget * (edgeBudget client.adjacency (vertexRange client.size) + 1) +
        model.popBudget * client.size.toNat ∧ client.parent < after.nextRef ∧
      client.caller.Footprint after [] [] [] := by
  let prepared := (before.write model client.key client.root 0).tick model "queue_updates"
  have preparedStorage : Storage model prepared :=
    (storage.write model _ client.root 0 (by simp [Client.protection])).tick model "queue_updates"
  obtain ⟨initial,inserted⟩ := queue_update model contracts prepared client.root 0 preparedStorage rootLower
    (by omega) (by intro key member; change (client.root,key) ∈ before.entries model at member; simp [empty] at member)
  have initialKeys : initial.heap.read client.key = fun _ => 0 := by
    rw [inserted.key]
    funext vertex
    change (before.heap.write client.key client.root 0).read client.key vertex = 0
    simpa [Heap.read,Heap.write] using
      congrArg (fun value => if vertex = client.root then 0 else value) (congrFun keys vertex)
  have initialParents : initial.heap.read client.parent = fun _ => -1 := by
    rw [inserted.parent]
    funext vertex
    change (before.heap.write client.key client.root 0).read client.parent vertex = -1
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (Ne.symm storage.keyParent)]
    exact congrFun parents vertex
  have initialFlags : initial.heap.read client.selected = fun _ => 0 := by
    rw [inserted.selected]
    funext vertex
    change (before.heap.write client.key client.root 0).read client.selected vertex = 0
    rw [Heap.read_write_other_ref _ _ _ _ _ _ (Ne.symm storage.separate)]
    exact congrFun flags vertex
  have invariant : LoopInvariant model initial (vertexRange client.size) := by
    refine ⟨inserted.storage,?_,⟨rootLower,rootUpper⟩,vertexRange_nodup client.size,?_,[],?_⟩
    · intro vertex key
      rw [inserted.contents,initialKeys,initialParents,initialFlags]
      change (vertex = client.root ∧ key = 0) ∨ (vertex ≠ client.root ∧ (vertex,key) ∈ before.entries model) ↔ _
      simp [empty]
    · intro vertex
      rw [initialFlags]
      simp
    · rw [initialParents,initialFlags]
      simpa only [ne_self_iff_false] using
        Algo2Lean.Prim.Invariant.initial (inputEdges client.size client.adjacency) client.root (initial.heap.read client.key)
  obtain ⟨after,completed⟩ := extraction_loop model contracts capacity symmetric initial (vertexRange client.size) invariant
  obtain ⟨pending,finalInvariant⟩ := completed.invariant
  obtain ⟨chosen,math⟩ := finalInvariant.mathematical
  have rootInside : after.heap.read client.selected client.root ≠ 0 := by
    intro absent
    have entry := (finalInvariant.matching client.root (after.heap.read client.key client.root)).mpr
      ⟨absent,Or.inl rfl,rfl⟩
    simp [completed.empty] at entry
  have noKeys : ∀ vertex, ¬ after.heap.read client.selected vertex ≠ 0 → after.heap.read client.parent vertex < 0 := by
    intro vertex outside
    by_cases known : 0 ≤ after.heap.read client.parent vertex
    · have entry := (finalInvariant.matching vertex (after.heap.read client.key vertex)).mpr
        ⟨by simpa using outside,Or.inr known,rfl⟩
      simp [completed.empty] at entry
    · omega
  have correct := math.finish (storage.graph.inputEdges_reverse symmetric) storage.graph.validInput connected
    rootLower (by have sizeNonnegative := storage.graph.sizeNonnegative; omega) rootInside noKeys
  have bounds : CostBounds model initial after client.size.toNat
      (edgeBudget client.adjacency (vertexRange client.size)) := by
    simpa only [vertexRange_length] using completed.costs
  have initialClocks (name) (member : name ∈ reservedClocks) := inserted.bookkeeping name member
  refine ⟨after.heap.tick "queue_empty_checks",?_,
    finalInvariant.storage.graph.preserved (graph_frame_tick _ _ _ "queue_empty_checks" 1),correct,?_,?_,
    finalInvariant.storage.parentAllocated,
    (model.callerPreserved finalInvariant.storage.queue).tick "queue_empty_checks"⟩
  · exact initialize_summary dependencies before.heap initial.heap (after.heap.tick "queue_empty_checks")
      client.graph client.root client.queue client.key client.parent client.selected
      ⟨storage.graph.valid,model.valid storage.queue,storage.keyAllocated,storage.parentAllocated,storage.selectedAllocated⟩
      inserted.execution completed.execution
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have clocks := initialClocks "queue_updates" (by simp [reservedClocks])
      have count := bounds.updates
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "queue_pops" (by simp [reservedClocks])
      have count := bounds.pops
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "queue_empty_checks" (by simp [reservedClocks])
      have count := bounds.checks
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "edges" (by simp [reservedClocks])
      have count := bounds.visits
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "improvements" (by simp [reservedClocks])
      have count := bounds.improvements
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
    · have clocks := initialClocks "settlements" (by simp [reservedClocks])
      have count := bounds.settlements
      simp [prepared,QueueState.tick,QueueState.write,Heap.cost,Heap.tick,Heap.write] at clocks count ⊢
      omega
  · have initialBound := inserted.amortized
    change work model ((before.heap.write client.key client.root 0).tick "queue_updates") initial.heap + _ ≤ _ at initialBound
    rw [work_tick_left model contracts _ _ "queue_updates" (by simp [reservedClocks])] at initialBound
    change work model before.heap initial.heap + initial.potential model ≤ before.potential model + model.updateBudget at initialBound
    have finalBound := bounds.amortized
    have triangle := work_triangle model before.heap initial.heap after.heap
    rw [work_tick_right model contracts _ _ "queue_empty_checks" (by simp [reservedClocks])]
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end PrimAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {dependencies : Algo.prim.prim.Dependencies} {client : PrimAnalysis.Client}
      (model : PriorityQueueAnalysis.Model dependencies.PriorityQueue client.queue client.protection),
      PriorityQueueAnalysis.Contracts model PrimAnalysis.reservedClocks →
        LE.le.{0} client.size model.capacity →
          ∀ (before : PrimAnalysis.QueueState model),
            PrimAnalysis.Storage model before →
              Eq.{1} (PrimAnalysis.QueueState.entries model before) List.nil.{0} →
                (Eq.{1} (before.heap.read client.key) fun x => (0 : Int)) →
                  (Eq.{1} (before.heap.read client.parent) fun x => (-1 : Int)) →
                    (Eq.{1} (before.heap.read client.selected) fun x => (0 : Int)) →
                      LE.le.{0} (0 : Int) client.root →
                        LT.lt.{0} client.root client.size →
                          PrimGraph.Symmetric client.size client.adjacency →
                            Algo2Lean.Kruskal.ConnectedOn client.size.toNat
                                (PrimGraph.inputEdges client.size client.adjacency) →
                              Exists.{1} fun after =>
                                Algo.prim.prim.prim.Call dependencies before.heap
                                    (Prod.mk.{0, 0} client.graph
                                      (Prod.mk.{0, 0} client.root
                                        (Prod.mk.{0, 0} client.queue
                                          (Prod.mk.{0, 0} client.key
                                            (Prod.mk.{0, 0} client.parent client.selected)))))
                                    after client.parent ∧
                                  PrimGraph.GraphRep after client.graph client.size client.heads
                                      client.adjacency ∧
                                    PrimAnalysis.MinimumSpanningParents client.size client.adjacency
                                        client.root (after.read client.parent) ∧
                                      PrimAnalysis.OperationCounts before.heap after client.size.toNat
                                          (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                            (Algo2Lean.Dijkstra.vertexRange client.size)) ∧
                                        LE.le.{0} (PrimAnalysis.work model before.heap after)
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (PrimAnalysis.QueueState.potential model before)
                                                (HMul.hMul.{0, 0, 0} model.updateBudget
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                                      (Algo2Lean.Dijkstra.vertexRange client.size))
                                                    (1 : Nat))))
                                              (HMul.hMul.{0, 0, 0} model.popBudget client.size.toNat)) ∧
                                          LT.lt.{0} client.parent after.nextRef ∧
                                            client.caller.Footprint after List.nil.{0} List.nil.{0}
                                              List.nil.{0} :=
  PrimAnalysis.prim_complete
