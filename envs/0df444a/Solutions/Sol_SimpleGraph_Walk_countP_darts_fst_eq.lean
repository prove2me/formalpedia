-- Prove2me | solution 1 for SimpleGraph.Walk.countP_darts_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:13.619582+00:00
-- url     : https://prove2.me/submissions/1bb46073-accd-487b-9f41-912a206529c3

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation
public import Theorems.Thm_SimpleGraph_Walk_countP_darts_fst_add

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
namespace Walk
theorem _root_.solution {u : V} (p : G.Walk u u) (v : V) :
    p.darts.countP (fun d => d.fst = v) = p.darts.countP (fun d => d.snd = v) := by
  have := p.countP_darts_fst_add v
  omega
end Walk
end SimpleGraph
