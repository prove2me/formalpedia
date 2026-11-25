-- Prove2me | solution 1 for PI.Mk.charpoly_dvd_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:47.642542+00:00
-- url     : https://prove2.me/submissions/1e985f29-1f6e-4c8e-b519-e7f427d8ac47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution {R : Type*} [CommRing R] {N : ℕ} (A : Matrix (Fin N) (Fin N) R)
    (n : ℕ) (h : A ^ n = 1) : A.charpoly ∣ (X ^ n - 1 : R[X]) ^ N := by
  have hcomm : Commute (scalar (Fin N) (X : R[X])) ((C : R →+* R[X]).mapMatrix A) :=
    scalar_commute (r := (X : R[X])) (fun r' => Commute.all _ r') _
  have hMn : ((C : R →+* R[X]).mapMatrix A) ^ n = 1 := by rw [← map_pow, h, map_one]
  have key : (∑ i ∈ Finset.range n, scalar (Fin N) (X : R[X]) ^ i *
      ((C : R →+* R[X]).mapMatrix A) ^ (n - 1 - i)) *
      (scalar (Fin N) (X : R[X]) - (C : R →+* R[X]).mapMatrix A)
      = scalar (Fin N) ((X : R[X]) ^ n - 1) := by
    rw [hcomm.geom_sum₂_mul, hMn, map_sub, map_pow, map_one]
  have hs : ∀ c : R[X], (scalar (Fin N) c).det = c ^ N := by
    intro c
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine Dvd.intro_left (∑ i ∈ Finset.range n, scalar (Fin N) (X : R[X]) ^ i *
      ((C : R →+* R[X]).mapMatrix A) ^ (n - 1 - i)).det ?_
  rw [← hs ((X : R[X]) ^ n - 1), ← key, det_mul]
  rfl
end PI.Mk
