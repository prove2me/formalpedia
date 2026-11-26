-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_finrankSubspaces_mul_frameProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:07.355431+00:00
-- url     : https://prove2.me/submissions/c0034dba-df67-492d-b94d-c5af0b517b2d

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_linearIndependentFrames

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
      frameProd (Fintype.card K) (Module.finrank K V) k := by
  letI : Fintype (FinrankSubspaces K V k) := Fintype.ofFinite _
  calc
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
        ∑ W : FinrankSubspaces K V k, frameProd (Fintype.card K) k k := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [Nat.card_eq_fintype_card]
    _ = ∑ W : FinrankSubspaces K V k,
          Nat.card (LinearIndependentFrames K W.1 k) := by
        apply Finset.sum_congr rfl
        intro W hW
        symm
        simpa [W.2] using
          (card_linearIndependentFrames (K := K) (V := W.1) (k := k)
            (by simp [W.2]))
    _ = Nat.card (Σ W : FinrankSubspaces K V k,
          LinearIndependentFrames K W.1 k) := Nat.card_sigma.symm
    _ = Nat.card (LinearIndependentFrames K V k) :=
      Nat.card_congr (linearIndependentFramesEquiv K V k).symm
    _ = frameProd (Fintype.card K) (Module.finrank K V) k :=
      card_linearIndependentFrames hk
end SharpIntermediateSubgroupBounds
