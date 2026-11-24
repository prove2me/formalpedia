-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.induce_union_geodesic_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:43.531693+00:00
-- url     : https://prove2.me/submissions/8697ef6b-48c8-4380-9fbc-7bf370adc273

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_SimpleGraph_IsTree_induce_insert_of_unique_adj


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) (s : Finset α)
    (hs : (G.induce (s : Set α)).IsTree) (hv : v ∈ s)
    (hinter : ∀ z ∈ p.support, z ∈ s → z = v)
    (hcross : ∀ z ∈ p.support, z ≠ v → ∀ w ∈ s, G.Adj z w → w = v) :
    (G.induce ((p.support.toFinset ∪ s : Finset α) : Set α)).IsTree := by
  induction p with
  | @nil u =>
    have hset : (Walk.nil : G.Walk u u).support.toFinset ∪ s = s := by
      ext z
      simp only [Finset.mem_union, List.mem_toFinset, Walk.support_nil, List.mem_singleton]
      exact or_iff_right_of_imp (fun hzu => hzu ▸ hv)
    rw [hset]
    exact hs
  | @cons u n v hun p ih =>
    have hptail : p.length = G.dist n v :=
      length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p hun)
    have hpPath := (p.cons hun).isPath_of_length_eq_dist hp
    have hu_not : u ∉ p.support.toFinset := by
      simpa using (List.nodup_cons.mp hpPath.support_nodup).1
    have huv : u ≠ v := by
      intro heq
      exact hu_not (by simpa [heq])
    have hu_s : u ∉ s := by
      intro hu
      exact huv (hinter u (by simp) hu)
    have hT := ih hptail hv
      (fun z hz => hinter z (by simp [hz]))
      (fun z hz => hcross z (by simp [hz]))
    have huniq : ∀ b ∈ p.support.toFinset, G.Adj u b → b = n := by
      intro b hb hub
      have hb' : b ∈ p.support := by simpa using hb
      have hsum := dist_add_dist_eq_of_mem_geodesic p hptail hb'
      have htri := hG.dist_triangle (u := u) (v := b) (w := v)
      have hubdist : G.dist u b = 1 := dist_eq_one_iff_adj.mpr hub
      have hlen : G.dist u v = G.dist n v + 1 := by
        simpa only [Walk.length_cons, hptail] using hp.symm
      have hn : G.dist n b = 0 := by omega
      exact (hG.dist_eq_zero_iff.mp hn).symm
    have hT' := hT.induce_insert_of_unique_adj
      (by simp only [Finset.mem_union, not_or]; exact ⟨hu_not, hu_s⟩)
      (Finset.mem_union_left _ (by simp)) hun (by
        intro b hb hub
        rcases Finset.mem_union.mp hb with hb | hb
        · exact huniq b hb hub
        · have hbv := hcross u (by simp) huv b hb hub
          exact huniq b (by simp [hbv]) hub)
    have hset : (p.cons hun).support.toFinset ∪ s = insert u (p.support.toFinset ∪ s) := by
      ext z
      simp
    rw [hset]
    exact hT'
end WrittenOnTheWallII.GraphConjecture84
