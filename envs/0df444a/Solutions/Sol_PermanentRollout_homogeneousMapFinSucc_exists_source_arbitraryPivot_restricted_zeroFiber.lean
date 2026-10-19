-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSucc_exists_source_arbitraryPivot_restricted_zeroFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/e7556055-69bb-4188-885c-30050f3281eb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_linearCoordinatePolynomial_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccArbitraryPivotPlaneMap_restricted_zeroFiber
import Theorems.Thm_PermanentRollout_homogeneousMapFinSucc_source_prefix_plane_data

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
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    ∃ (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)),
      c j ≠ 0 ∧
      (∀ i : Fin n,
        (MvPolynomial.aeval
          (fun row => linearCoordinatePolynomial
            (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row)
          (F i.castSucc)).IsHomogeneous e) ∧
      (∀ u : Fin n → ℂ,
        (∀ i : Fin n,
          MvPolynomial.eval u
            (MvPolynomial.aeval
              (fun row => linearCoordinatePolynomial
                (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row)
              (F i.castSucc)) = 0) ↔ u = 0) := by
  classical
  obtain ⟨c, hc, hslicedZero⟩ :=
    homogeneousMapFinSucc_source_prefix_plane_data F e he hF hzero
  have hc0 : c 0 ≠ 0 := hc.ne_zero 0
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), c 0 j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hc0 (funext fun i => h i)
  have hrange :
      Set.range (fun i : Fin 1 =>
        permanentRolloutLinearCoordinateCombination (n + 1) (c i)) =
      Set.range (fun _ : Fin 1 =>
        permanentRolloutLinearCoordinateCombination (n + 1) (c 0)) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i = 0 := Subsingleton.elim i 0
      exact ⟨0, by simp [hi]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨0, rfl⟩
  have hradical :
      ((Ideal.span (Set.range fun i : Fin n => F i.castSucc)) ⊔
        Ideal.span (Set.range fun _ : Fin 1 =>
          permanentRolloutLinearCoordinateCombination (n + 1)
            (c 0))).radical =
        MvPolynomial.idealOfVars (Fin (n + 1)) ℂ := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    have hzeroPlane :
        MvPolynomial.zeroLocus ℂ
          ((Ideal.span (Set.range fun i : Fin n => F i.castSucc)) ⊔
            Ideal.span (Set.range fun _ : Fin 1 =>
              permanentRolloutLinearCoordinateCombination (n + 1)
                (c 0))) =
          ({0} : Set (Fin (n + 1) → ℂ)) := by
      rw [← hrange]
      exact hslicedZero
    rw [hzeroPlane, vanishingIdeal_origin_eq_idealOfVars]
  refine ⟨c 0, j, hj, ?_,
    homogeneousMapFinSuccArbitraryPivotPlaneMap_restricted_zeroFiber
      F e he hF (c 0) j hj hradical⟩
  intro i
  simpa using (hF i.castSucc).aeval
    (fun row => linearCoordinatePolynomial
      (homogeneousMapFinSuccArbitraryPivotPlaneMap (c 0) j) row)
    (fun row => linearCoordinatePolynomial_isHomogeneous
      (homogeneousMapFinSuccArbitraryPivotPlaneMap (c 0) j) row)
end PermanentRollout
