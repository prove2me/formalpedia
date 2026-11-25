-- Prove2me | solution 1 for PIW.CMDiscSq.minpoly_eq_of_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:18.388832+00:00
-- url     : https://prove2.me/submissions/25eebc44-39b7-4822-9cbe-3fcff501e12b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe
import Theorems.Thm_PIW_CMDiscSq_exists_of_star_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    [FiniteDimensional F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    ∃ s n : F, algebraMap F E s = x + star x ∧ algebraMap F E n = x * star x ∧
      minpoly F x = X ^ 2 - C s * X + C n := by
  obtain ⟨s, hs⟩ := exists_of_star_eq hR (y := x + star x) (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := exists_of_star_eq hR (y := x * star x) (by rw [star_mul', star_star, mul_comm])
  refine ⟨s, n, hs, hn, ?_⟩
  have hmon : (X ^ 2 - C s * X + C n : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 - C s * X + C n : F[X]).natDegree = 2 := by compute_degree!
  have hroot : aeval x (X ^ 2 - C s * X + C n : F[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h2 : 2 ≤ (minpoly F x).natDegree := by
    rw [minpoly.two_le_natDegree_iff hint]
    rintro ⟨a, rfl⟩
    apply hx
    have : algebraMap F E a ∈ Set.range (algebraMap F E) := ⟨a, rfl⟩
    rw [hR] at this
    exact this
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon
    (minpoly.dvd F x hroot) (by rw [hdeg]; exact h2)).symm
end PIW.CMDiscSq
