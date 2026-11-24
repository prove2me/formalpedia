-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.adjacent_start_eq_snd_of_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:29:43.85669+00:00
-- url     : https://prove2.me/submissions/58da742d-c066-4eb9-a46e-2da10294a291

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {c b z : α} (q : G.Walk c b) (hq : q.length = G.dist c b)
    (hz : z ∈ q.support) (hcz : G.Adj c z) : z = q.snd := by
  cases q with
  | nil =>
    have hzc : z = c := by simpa using hz
    exact (hcz.ne hzc.symm).elim
  | @cons c n b hcn q =>
    have hzq : z ∈ q.support := (List.mem_cons.mp hz).resolve_left hcz.ne.symm
    have hqt : q.length = G.dist n b :=
      length_eq_dist_of_subwalk hq (Walk.isSubwalk_cons q hcn)
    have hsum := dist_add_dist_eq_of_mem_geodesic q hqt hzq
    have htri := hG.dist_triangle (u := c) (v := z) (w := b)
    have hczd : G.dist c z = 1 := dist_eq_one_iff_adj.mpr hcz
    have hlen : G.dist c b = G.dist n b + 1 := by
      simpa only [Walk.length_cons, hqt] using hq.symm
    have hnz : G.dist n z = 0 := by omega
    simpa using (hG.dist_eq_zero_iff.mp hnz).symm
end WrittenOnTheWallII.GraphConjecture84
