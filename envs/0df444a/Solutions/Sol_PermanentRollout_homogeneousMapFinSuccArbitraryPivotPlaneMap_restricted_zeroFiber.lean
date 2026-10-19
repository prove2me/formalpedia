-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_restricted_zeroFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/3076786c-f94d-4d00-9a94-666427636a8e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_eval_zero_of_pos
import Theorems.Thm_PermanentRollout_eval_aeval_linearCoordinatePolynomial
import Theorems.Thm_PermanentRollout_eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccArbitraryPivotPlaneMap_injective
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccArbitraryPivotPlaneMap_kernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1)) (hj : c j ≠ 0)
    (hradical :
      ((Ideal.span (Set.range fun i : Fin n => F i.castSucc)) ⊔
        Ideal.span (Set.range fun _ : Fin 1 =>
          permanentRolloutLinearCoordinateCombination (n + 1) c)).radical =
        MvPolynomial.idealOfVars (Fin (n + 1)) ℂ) :
    ∀ u : Fin n → ℂ,
      (∀ i : Fin n,
        MvPolynomial.eval u
          (MvPolynomial.aeval
            (fun row => linearCoordinatePolynomial
              (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row)
            (F i.castSucc)) = 0) ↔ u = 0 := by
  classical
  intro u
  constructor
  · intro hu
    let W := homogeneousMapFinSuccArbitraryPivotPlaneMap c j
    let I : Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
      Ideal.span (Set.range fun i : Fin n => F i.castSucc)
    have hvanishing : W u ∈ MvPolynomial.zeroLocus ℂ I := by
      intro p hp
      have hs : I ≤ MvPolynomial.vanishingIdeal ℂ {W u} := by
        change Ideal.span (Set.range fun i : Fin n => F i.castSucc) ≤ _
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        change F i.castSucc ∈ MvPolynomial.vanishingIdeal ℂ {W u}
        rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
        exact (eval_aeval_linearCoordinatePolynomial W u
          (F i.castSucc)).symm.trans (hu i)
      exact hs hp (W u) (Set.mem_singleton _)
    have hkernel :
        Matrix.mulVecLin
          ((fun _ : Fin 1 => c) : Matrix (Fin 1) (Fin (n + 1)) ℂ)
            (W u) = 0 := by
      funext q
      fin_cases q
      change (∑ i : Fin (n + 1), c i * W u i) = 0
      exact homogeneousMapFinSuccArbitraryPivotPlaneMap_kernel c j hj u
    have hWu : W u = 0 :=
      eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
        I (fun _ : Fin 1 => c) hradical hvanishing hkernel
    exact homogeneousMapFinSuccArbitraryPivotPlaneMap_injective c j
      (hWu.trans (map_zero W).symm)
  · rintro rfl i
    rw [eval_aeval_linearCoordinatePolynomial,
      map_zero]
    exact homogeneous_eval_zero_of_pos he (hF i.castSucc)
end PermanentRollout
