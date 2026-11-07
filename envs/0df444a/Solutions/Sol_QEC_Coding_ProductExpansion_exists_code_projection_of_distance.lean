-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_code_projection_of_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:08.363723+00:00
-- url     : https://prove2.me/submissions/780be9a0-5355-45a4-84ec-08f8882a854a

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_restriction_injective_of_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_code_projection_of_restriction_injective

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
    ∃ T : Word F W →ₗ[F] Word F W,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) ∧
      (∀ x : Word F W, (∀ i ∈ A, x i = 0) → T x = 0) ∧
      (∀ x : Word F W, T x ∈ (parityCheckCode h).carrier) := by
  apply exists_code_projection_of_restriction_injective h A
  change Function.Injective (fun c : (parityCheckCode h).carrier =>
    fun i : {i : W // i ∈ A} => c.1 i.1)
  exact restriction_injective_of_distance h d hDistance A hLarge
end QEC.Coding.ProductExpansion
