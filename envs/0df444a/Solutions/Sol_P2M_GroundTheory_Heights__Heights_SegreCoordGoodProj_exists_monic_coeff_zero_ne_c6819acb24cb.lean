-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_exists_monic_coeff_zero_ne_c6819acb24cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:35.393858+00:00
-- url     : https://prove2.me/submissions/6a8d389c-a774-41de-8305-92e031a7854c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.SegreCoordGoodProj
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreCoordGoodProj
theorem _root_.solution {A R : Type*} [CommRing A] [Nontrivial A] [CommRing R] [IsDomain R]
    (f : A →+* R) {x : R} (hx : x ≠ 0) (h : f.IsIntegralElem x) :
    ∃ p : Polynomial A, p.Monic ∧ p.eval₂ f x = 0 ∧ p.coeff 0 ≠ 0 := by
  obtain ⟨p, hpm, hp⟩ := h
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.coeff 0 = 0
    · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
      have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hpm
      have hq : q.eval₂ f x = 0 := by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
        exact (mul_eq_zero.mp hp).resolve_left hx
      refine ih q.natDegree ?_ q hqm hq rfl
      rw [← hn, Polynomial.Monic.natDegree_mul Polynomial.monic_X hqm, Polynomial.natDegree_X]
      omega
    · exact ⟨p, hpm, hp, h0⟩
end GroundTheory.Heights₂.Heights.SegreCoordGoodProj
