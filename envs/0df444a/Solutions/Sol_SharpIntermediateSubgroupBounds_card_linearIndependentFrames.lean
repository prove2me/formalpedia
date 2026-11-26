-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_linearIndependentFrames
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:46:48.872806+00:00
-- url     : https://prove2.me/submissions/284a0342-efff-47a5-b97a-e5c5a735d4d6

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (LinearIndependentFrames K V k) =
      frameProd (Fintype.card K) (Module.finrank K V) k := by
  simpa [frameProd] using card_linearIndependent (K := K) (V := V) hk
end SharpIntermediateSubgroupBounds
