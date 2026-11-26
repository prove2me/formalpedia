-- Prove2me | solution 1 for P2M_DenseTriangleFree_sum_map_filter__6198be9b6b06
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:31.790677+00:00
-- url     : https://prove2.me/submissions/baf761b0-1b10-45c8-b76d-cad3a25176e5

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution {p : ℕ → Prop} [DecidablePred p] (L : List ℕ) (g : ℕ → ℕ) :
    ((L.filter fun i => decide (p i)).map g).sum =
      (L.map fun i => if p i then g i else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases h : p a <;> simp [h, ih]
end DenseTriangleFree
