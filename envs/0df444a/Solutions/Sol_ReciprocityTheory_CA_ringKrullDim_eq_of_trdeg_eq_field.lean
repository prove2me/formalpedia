-- Prove2me | solution 1 for ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:46:35.956438+00:00
-- url     : https://prove2.me/submissions/1a054327-bed3-4285-9f7d-3fa51eaac6d7

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u
namespace ReciprocityTheory.CA
theorem _root_.solution {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : Algebra.trdeg K A = n) :
    ringKrullDim A = n := by
  obtain ⟨s, h1, h2⟩ := exists_dim_trdeg_field (K := K) (A := A)
  rw [h2] at h
  have hs : s = n := by exact_mod_cast h
  rw [h1, hs]
end ReciprocityTheory.CA
