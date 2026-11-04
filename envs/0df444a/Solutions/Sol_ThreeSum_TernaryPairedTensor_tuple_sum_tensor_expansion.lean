-- Prove2me | solution 1 for ThreeSum.TernaryPairedTensor.tuple_sum_tensor_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:19.719361+00:00
-- url     : https://prove2.me/submissions/895746fe-f01a-41b8-9526-0870d47ea583

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Theorems.Thm_ThreeSum_TernaryPairedTensor_det_square_expansion

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]
namespace ThreeSum.TernaryPairedTensor
theorem _root_.solution {m : ℕ} (L R' : P → I → R)
    (cols : PairedIndex m → I) :
    (∑ e : Fin m → P, (pairedMinor L R' e cols).det^2) =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)) *
        ∏ i : Fin m, tensor L R' (cols (σ (.inl i))) (cols (τ (.inl i)))
          (cols (σ (.inr i))) (cols (τ (.inr i))) := by
  simp_rw [det_square_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ hσ
  rw [sum_comm]
  apply sum_congr rfl
  intro τ hτ
  rw [← mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun i (x : P) =>
    L x (cols (σ (.inl i))) * L x (cols (τ (.inl i))) *
      R' x (cols (σ (.inr i))) * R' x (cols (τ (.inr i))))).symm
end ThreeSum.TernaryPairedTensor
