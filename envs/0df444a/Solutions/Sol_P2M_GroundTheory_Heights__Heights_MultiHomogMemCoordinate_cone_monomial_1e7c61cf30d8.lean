-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_monomial_1e7c61cf30d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:43.894047+00:00
-- url     : https://prove2.me/submissions/9201f626-bd52-41f4-8425-4e34bb7e140c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PMultiHomogMemCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_mapDomain_fst_eq_d16f83d8ff63

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
open GroundTheory.Heights₂.Heights.MultiHomogMemCoordinate
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.MultiHomogMemCoordinate
theorem _root_.solution (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  have hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) =
      m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp only [map_pow, rename_X]
  rw [← mapDomain_fst_eq m a hm, hX]
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd,
    map_pow, map_mul]
  ring
end GroundTheory.Heights₂.Heights.MultiHomogMemCoordinate
