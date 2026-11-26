-- Prove2me | solution 1 for P2M_DenseTriangleFree_triangle_of_cliqueFree__32533396f53c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:24.317396+00:00
-- url     : https://prove2.me/submissions/f431e7e9-ba4c-4057-af5c-75d64355fcd8

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
public import Theorems.Thm_DenseTriangleFree_triangle_of_cliqueFree


set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution {V : Type*} {G : SimpleGraph V} (h3 : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False :=
  triangle_of_cliqueFree h3 hab hbc hca.symm
end DenseTriangleFree
