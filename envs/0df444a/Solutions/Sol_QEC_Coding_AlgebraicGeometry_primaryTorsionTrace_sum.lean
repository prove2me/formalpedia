-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:15.750689+00:00
-- url     : https://prove2.me/submissions/39f78306-811c-4e83-bbe1-f124214f0d1a

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PiTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    {ι : Type w} (s : Finset ι) (f : ι → M →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (∑ i ∈ s, f i) n =
      ∑ i ∈ s, primaryTorsionTrace p (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using primaryTorsionTrace_zero p n
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, primaryTorsionTrace_add, ih,
        Finset.sum_insert ha]
end QEC.Coding.AlgebraicGeometry
