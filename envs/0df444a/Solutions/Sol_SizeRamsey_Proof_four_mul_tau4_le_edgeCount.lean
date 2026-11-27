-- Prove2me | solution 1 for SizeRamsey.Proof.four_mul_tau4_le_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:48.1098+00:00
-- url     : https://prove2.me/submissions/cd334be2-7b66-4db2-ba17-f745557b9988

module
public import Definitions.Def_SizeRamsey_Reductions
public import Definitions.Def_SizeRamsey_Universal
public import Theorems.Thm_SizeRamsey_Plan_universal

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Proof
namespace SizeRamsey.Proof
theorem _root_.solution
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    4 * tau4 G ≤ edgeCount G := by
  exact Plan.universal G
end SizeRamsey.Proof
