-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.restriction_injective_of_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:02.273554+00:00
-- url     : https://prove2.me/submissions/2331c13c-3dea-49da-b500-64898e8a4fb6

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_vanish_on_large_subset

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (hLarge : Fintype.card W - d < A.card) :
    Function.Injective (fun c : (parityCheckCode h).carrier =>
      fun i : {i : W // i ∈ A} => c.1 i.1) := by
  intro c e heq
  have hdiff : c.1 - e.1 ∈ (parityCheckCode h).carrier :=
    (parityCheckCode h).carrier.sub_mem c.2 e.2
  have hvanish : ∀ i ∈ A, (c.1 - e.1) i = 0 := by
    intro i hi
    have hvalue := congrFun heq ⟨i, hi⟩
    exact sub_eq_zero.mpr hvalue
  have hzero := codeword_eq_zero_of_vanish_on_large_subset
    h d hDistance A hLarge (c.1 - e.1) hdiff hvanish
  apply Subtype.ext
  exact sub_eq_zero.mp hzero
end QEC.Coding.ProductExpansion
