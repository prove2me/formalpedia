-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSucc_source_prefix_plane_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/96ded5ae-8d9c-4b4e-8e15-c5d1334ab0f5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices

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
    ∃ c : Fin 1 → Fin (n + 1) → ℂ,
      LinearIndependent ℂ c ∧
      MvPolynomial.zeroLocus ℂ
        (Ideal.span (Set.range fun i : Fin n => F i.castSucc) ⊔
          Ideal.span (Set.range fun i : Fin 1 =>
            permanentRolloutLinearCoordinateCombination (n + 1) (c i))) =
        ({0} : Set (Fin (n + 1) → ℂ)) := by
  classical
  have hcard :
      (Finset.univ.erase (Fin.last n) : Finset (Fin (n + 1))).card = n := by
    simp
  have hslices :
      ∃ c : Fin 1 → Fin (n + 1) → ℂ,
        LinearIndependent ℂ c ∧
        MvPolynomial.zeroLocus ℂ
          (homogeneousLinearSliceIdeal
            (Ideal.span
              (F '' ((Finset.univ.erase (Fin.last n) :
                Finset (Fin (n + 1))) : Set (Fin (n + 1))))) c) =
          ({0} : Set (Fin (n + 1) → ℂ)) := by
    have h :=
      homogeneousMap_exists_coordinateSubset_independent_linear_origin_slices
        F e he hF hzero (Finset.univ.erase (Fin.last n))
    have hsub : n + 1 - n = 1 := by omega
    rw [hcard, hsub] at h
    exact h
  obtain ⟨c, hc, hslice⟩ := hslices
  have himage :
      F '' ((Finset.univ.erase (Fin.last n) :
        Finset (Fin (n + 1))) : Set (Fin (n + 1))) =
        Set.range (fun i : Fin n => F i.castSucc) := by
    ext p
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hlast : i ≠ Fin.last n := by
        simpa using hi
      obtain ⟨q, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
      exact ⟨q, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i.castSucc, ?_, rfl⟩
      simp
  refine ⟨c, hc, ?_⟩
  change MvPolynomial.zeroLocus ℂ
    (Ideal.span
      (F '' ((Finset.univ.erase (Fin.last n) :
        Finset (Fin (n + 1))) : Set (Fin (n + 1)))) ⊔
      Ideal.span (Set.range fun i : Fin 1 =>
        permanentRolloutLinearCoordinateCombination (n + 1) (c i))) =
    ({0} : Set (Fin (n + 1) → ℂ)) at hslice
  rw [himage] at hslice
  exact hslice
end PermanentRollout
