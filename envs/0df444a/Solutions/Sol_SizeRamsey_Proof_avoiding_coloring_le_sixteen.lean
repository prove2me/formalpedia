-- Prove2me | solution 1 for SizeRamsey.Proof.avoiding_coloring_le_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:39:52.809823+00:00
-- url     : https://prove2.me/submissions/dcaf0f4f-d2bf-4c9c-a9c6-8100030b11f4

module
public import Definitions.Def_SizeRamsey_Equality
public import Definitions.Def_SizeRamsey_ColoringBase
public import Definitions.Def_SizeRamsey_Coloring
public import Theorems.Thm_SizeRamsey_Proof_connected_transversal_le_three
public import Theorems.Thm_SizeRamsey_avoiding_coloring_of_transversal


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
open SizeRamsey.Proof
namespace SizeRamsey.Proof
theorem _root_.solution
    {V : Type*} [Fintype V] (F : SimpleGraph V)
    (hconn : F.Connected) (hle : edgeCount F ≤ 16) :
    ∃ R : SimpleGraph V,
      R ≤ F ∧ ¬ HasMatching4 R ∧ ¬ HasC4 (F \ R) := by
  obtain ⟨S, hS, hcard⟩ := connected_transversal_le_three F hconn hle
  exact avoiding_coloring_of_transversal F S hS hcard
end SizeRamsey.Proof
