-- Prove2me | solution 1 for ThreeSumApsp.TriangleInstance.card_instanceIndices
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:30:04.154135+00:00
-- url     : https://prove2.me/submissions/a3d8b6e7-17be-4964-9320-09608343cc7a

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Theorem 17, second step: the instances

With `s = ⌊√D⌋`, the part `C` is split into `h` pieces of at most `⌈s/g⌉` vertices, the pairs
`(a,b)` are grouped by `ϱ = w(a,b) mod p` into the sets `W_ϱ`, and every `W_ϱ` is cut into chunks of
at most `n²/√D` pairs.  There is one instance of Lop-AE-SparseTri(n, D) for each chunk and each
piece.  As in the paper:

* the pieces, and `h ≤ ⌈ng/s⌉` (`existsUnique_mem_piece`, `card_piece_le`,
  `numPieces_le`);
* the sets `W_ϱ` and their chunks (`TriangleInstance.existsUnique_mem_residueClass`,
  `TriangleInstance.card_chunkOf_le`);
* there are at most `p + √D ≤ 2√D` chunks in all (`TriangleInstance.totalChunks_le`); as a chunk
  holds a whole number of pairs, this rests on `n² < (s + 1)⌊n²/√D⌋ + p` (`sq_lt_mul_queryCap_add`);
* the middle part has at most `sp ≤ D` vertices (`TriangleInstance.middleAtMost_lopInstance`);
* within a chunk, `S(a,b,c) ≡ 0 (mod p)` is an equality of labels
  (`TriangleInstance.S_modEq_zero_iff`), so a query pair has a common neighbor if and only if some
  `c` in the piece has `S(a,b,c) ≡ 0 (mod p)` (`TriangleInstance.inTriangle_lopInstance_iff`);
* there are at most `2√D h ≤ 4ng` instances (`le_sOf_and_sqrt_le`,
  `TriangleInstance.card_instanceIndices_le`).

The file ends with a remark of Section 3.1 and of Remark 20: a vertex of `A` or `B` has at most
`⌈s/g⌉` neighbors in an instance (`TriangleInstance.ncard_nbr_lopInstance_le`).  Nothing else rests
on it.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

/-! ### The pieces -/



















































/-! ### Residues -/



















/-! ### The arithmetic behind the two counts -/















































































namespace TriangleInstance

variable (T : TriangleInstance ℤ n)

/-! ### The sets `W_ϱ` -/





























/-! ### The chunks -/









































/-! ### The instances -/






























































/-- There are as many instances as chunks times pieces. -/
theorem card_instanceIndices_sourceProof (D g p : ℕ) :
    (T.instanceIndices D g p).card = T.totalChunks D p * numPieces n D g := by
  unfold instanceIndices totalChunks
  rw [Finset.card_biUnion, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun ϱ _ => ?_
    rw [Finset.card_image_of_injective _ (Prod.mk_right_injective ϱ), Finset.card_product,
      Finset.card_range, Finset.card_range]
  · intro ϱ _ ϱ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx'
    exact hne (congrArg Prod.fst h).symm




























end TriangleInstance

/-! ### The neighborhoods in an instance -/






































end ThreeSumApsp

end


theorem solution : ∀ {n : Nat} (T : ThreeSumApsp.TriangleInstance Int n) (D g p : Nat),
  @Eq.{1} Nat
    (@Finset.card.{0} (ThreeSumApsp.InstanceIndex p) (@ThreeSumApsp.TriangleInstance.instanceIndices n T D g p))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@ThreeSumApsp.TriangleInstance.totalChunks n T D p) (ThreeSumApsp.numPieces n D g)) := by
  exact @ThreeSumApsp.TriangleInstance.card_instanceIndices_sourceProof

#print axioms solution
