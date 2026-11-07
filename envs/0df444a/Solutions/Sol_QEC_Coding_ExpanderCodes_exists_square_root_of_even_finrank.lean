-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_square_root_of_even_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:45:40.774848+00:00
-- url     : https://prove2.me/submissions/f2893274-4b26-479e-9366-fabbc32cfb22

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open scoped QuadraticAlgebra
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution
    {F K : Type*} [Field F] [Field K] [Finite K] [Algebra F K]
    (epsilon : F) (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEven : 2 ∣ Module.finrank F K) :
    ∃ r : K, r ^ 2 = algebraMap F K epsilon := by
  letI : Fact (∀ r : F, r ^ 2 ≠ epsilon + 0 * r) :=
    ⟨fun r => by simpa using hNonSquare r⟩
  obtain ⟨g⟩ : Nonempty (QuadraticAlgebra F epsilon 0 →ₐ[F] K) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      simpa only [QuadraticAlgebra.finrank_eq_two] using hEven)
  let i : QuadraticAlgebra F epsilon 0 := ⟨0, 1⟩
  have hSquare : i ^ 2 = algebraMap F (QuadraticAlgebra F epsilon 0) epsilon := by
    ext <;> simp [i, pow_two]
  refine ⟨g i, ?_⟩
  calc
    (g i) ^ 2 = g (i ^ 2) := (map_pow g i 2).symm
    _ = g (algebraMap F (QuadraticAlgebra F epsilon 0) epsilon) := congrArg g hSquare
    _ = algebraMap F K epsilon := g.commutes epsilon
end QEC.Coding.ExpanderCodes
