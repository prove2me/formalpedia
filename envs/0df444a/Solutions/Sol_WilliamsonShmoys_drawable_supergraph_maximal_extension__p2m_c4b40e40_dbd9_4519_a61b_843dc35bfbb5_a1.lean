-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_maximal_extension__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:41.280079+00:00
-- url     : https://prove2.me/submissions/1987ed17-c3d1-46b1-b0cc-e338d6478866

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
import Theorems.Thm_finite_simpleGraph_of_fintype__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      And (LE.le L M) (And (WilliamsonShmoys.HasPlanarDrawingOn M)
        (forall N : SimpleGraph V, LE.le M N ->
          WilliamsonShmoys.HasPlanarDrawingOn N -> N = M)) := by
  let S : Type := {M : SimpleGraph V // And (LE.le L M) (WilliamsonShmoys.HasPlanarDrawingOn M)}
  letI : Finite (SimpleGraph V) :=
    finite_simpleGraph_of_fintype__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
  letI : Finite S := inferInstance
  let a : S := Subtype.mk L (And.intro le_rfl hL)
  let b : S := Classical.choose
    (finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2 a)
  have hmax : forall c : S, LE.le b c -> c = b :=
    (Classical.choose_spec
      (finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2 a)).2
  apply Exists.intro b.1
  apply And.intro b.2.1
  apply And.intro b.2.2
  intro N hMN hN
  let N' : S := Subtype.mk N (And.intro (le_trans b.2.1 hMN) hN)
  have hN'b : LE.le b N' := hMN
  have hEq : N' = b := hmax N' hN'b
  exact congrArg Subtype.val hEq