-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_coeff_sum_C_mul_prod_X_pow_6099e2d14792
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:39.240274+00:00
-- url     : https://prove2.me/submissions/e3ad184d-0ce8-4ac3-8ad1-f74061252337

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_prod_X_pow_eq_monomial_fintype_a59d57b5530c

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution {D : Type*} [CommRing D] (S : Finset (ι → ℕ))
    (a : (ι → ℕ) → D) {d : ι → ℕ} (hd : d ∈ S) :
    coeff (Finsupp.equivFunOnFinite.symm d) (∑ e ∈ S, C (a e) * ∏ k, (X k : MvPolynomial ι D) ^ e k) =
      a d := by
  classical
  simp only [prod_X_pow_eq_monomial_fintype, coeff_sum, coeff_C_mul, coeff_monomial,
    EmbeddingLike.apply_eq_iff_eq, mul_ite, mul_one, mul_zero]
  simp [hd]
end GroundTheory.Heights₂.Heights.OrbitChartMult
