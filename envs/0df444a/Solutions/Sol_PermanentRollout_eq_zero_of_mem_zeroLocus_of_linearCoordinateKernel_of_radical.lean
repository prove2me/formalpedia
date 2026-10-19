-- Prove2me | solution 1 for PermanentRollout.eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/b604a9b5-175e-4370-b821-28367f82b0fd

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ)
    (hradical :
      (I ⊔ Ideal.span (Set.range fun j =>
        permanentRolloutLinearCoordinateCombination m (c j))).radical =
        MvPolynomial.idealOfVars (Fin m) ℂ)
    {v : Fin m → ℂ}
    (hv : v ∈ MvPolynomial.zeroLocus ℂ I)
    (hkernel : Matrix.mulVecLin (c : Matrix (Fin n) (Fin m) ℂ) v = 0) :
    v = 0 := by
  let J : Ideal (MvPolynomial (Fin m) ℂ) :=
    I ⊔ Ideal.span (Set.range fun j =>
      permanentRolloutLinearCoordinateCombination m (c j))
  have hvanishing : J ≤ MvPolynomial.vanishingIdeal ℂ {v} := by
    apply sup_le
    · intro f hf
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      exact hv f hf
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      change permanentRolloutLinearCoordinateCombination m (c j) ∈
        MvPolynomial.vanishingIdeal ℂ {v}
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      have hj := congrFun hkernel j
      change (∑ i, c j i * v i) = 0 at hj
      simpa [permanentRolloutLinearCoordinateCombination,
        MvPolynomial.aeval_def, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, smul_eq_mul] using hj
  have hvJ : v ∈ MvPolynomial.zeroLocus ℂ J := by
    intro f hf
    exact hvanishing hf v (Set.mem_singleton v)
  funext i
  have hXi : MvPolynomial.X i ∈ J.radical := by
    change MvPolynomial.X i ∈
      (I ⊔ Ideal.span (Set.range fun j =>
        permanentRolloutLinearCoordinateCombination m (c j))).radical
    rw [hradical, MvPolynomial.idealOfVars]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hzero :=
    (MvPolynomial.radical_le_vanishingIdeal_zeroLocus (K := ℂ) J hXi)
      v hvJ
  simpa [MvPolynomial.aeval_def] using hzero
end PermanentRollout
