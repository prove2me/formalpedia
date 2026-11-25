-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_IsVerticalDivisorAt_ofPrime_733ffd7ef5f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:21.156257+00:00
-- url     : https://prove2.me/submissions/3b23107c-03b8-4a8c-b9b2-5a9c8e632aaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_C_zero_b41b49555e2b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
namespace IsVerticalDivisorAt
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsHorizontal P) {p : ℕ}
    (hp : p ≠ 0) : IsVerticalDivisorAt P p 0 (C (p : ℤ)) 1 where
  degrees := ⟨0, 0, isMultiHomog_C_zero _, by simpa using isMultiHomog_C_zero (ι := ι) 1, by
    funext k; simp⟩
  num_not_mem := fun h => by
    have : (p : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hP, Ideal.mem_bot] at this
    exact hp (by exact_mod_cast this)
  den_not_mem := fun h => by
    have : (1 : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := by simpa [Ideal.mem_comap] using h
    rw [hP, Ideal.mem_bot] at this
    exact one_ne_zero this
  unit_off_fibre := fun W hW _ _ hpW =>
    ⟨1, C (p : ℤ), fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h), hpW, by simp⟩
end IsVerticalDivisorAt
end GroundTheory.Heights₂.Heights.LowerBoundFree
