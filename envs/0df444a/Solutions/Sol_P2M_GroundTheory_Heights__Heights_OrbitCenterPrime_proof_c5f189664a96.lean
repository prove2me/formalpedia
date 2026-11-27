-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCenterPrime_proof_c5f189664a96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:22:45.588569+00:00
-- url     : https://prove2.me/submissions/f3470197-6656-447a-ac35-a3d75d4ffa32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
namespace OrbitCenterPrime
theorem _root_.solution (hIff : OrbitCenterMemIff.Statement) :
    OrbitCenterPrime.Statement := by
  intro ι _ _ n x hx v
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let w : Coord n → Lex (ι → ℕ) := fun c ↦ toLex (coordDeg n c)
  let _ : DecidableEq (Lex (ι → ℕ)) := LinearOrder.toDecidableEq
  have _ : GradedRing (weightedHomogeneousSubmodule ℤ w) := MvPolynomial.weightedGradedAlgebra ℤ w
  have hw : ∀ (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
      IsWeightedHomogeneous w F (toLex d) ↔ IsWeightedHomogeneous (coordDeg n) F d :=
    fun _ _ ↦ Iff.rfl
  set M : (ι → ℕ) → ℝ := fun d ↦ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k with hM
  have hM0 : ∀ d, 0 ≤ M d := fun d ↦
    Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _
  have hMadd : ∀ d e, M (d + e) = M d * M e := fun d e ↦ by
    simp only [hM, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hform : ∀ F, SetLike.IsHomogeneousElem (weightedHomogeneousSubmodule ℤ w) F →
      ∃ d, Geo.IsMultiHomog (ι := blockIdx n) F d := by
    rintro F ⟨i, hi⟩
    exact ⟨ofLex i, (geoMultiHomog_iff _ _).mpr
      ((hw F (ofLex i)).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hi))⟩
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule ℤ w) ?_ ?_ ?_
  · refine Ideal.homogeneous_span _ _ ?_
    rintro F ⟨d, hd, -⟩
    exact ⟨toLex d, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      ((hw F d).mpr ((geoMultiHomog_iff _ _).mp hd))⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    intro h
    have h1 : Geo.IsMultiHomog (ι := blockIdx n) (1 : MvPolynomial (Coord n) ℤ) 0 :=
      (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_one ℤ _)
    have := (hIff ι n x hx v 1 0 h1).mp h
    simp [evalCone] at this
  · intro F G hF hG hFG
    obtain ⟨d, hd⟩ := hform F hF
    obtain ⟨e, he⟩ := hform G hG
    have hde : Geo.IsMultiHomog (ι := blockIdx n) (F * G) (d + e) :=
      (geoMultiHomog_iff _ _).mpr
        (((geoMultiHomog_iff _ _).mp hd).mul ((geoMultiHomog_iff _ _).mp he))
    have hlt := (hIff ι n x hx v _ _ hde).mp hFG
    by_contra! hno
    have h1 := not_lt.mp (mt (hIff ι n x hx v F d hd).mpr hno.1)
    have h2 := not_lt.mp (mt (hIff ι n x hx v G e he).mpr hno.2)
    rw [evalCone, eval₂_mul, map_mul, ← evalCone, ← evalCone] at hlt
    have := mul_le_mul h1 h2 (hM0 e) (apply_nonneg v _)
    rw [← hMadd] at this
    exact absurd hlt (not_lt.mpr this)
end OrbitCenterPrime
end GroundTheory.Heights₂.Heights
