-- Prove2me | solution 1 for ReciprocityTheory.CA.comap_C_eq_maximalIdeal_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:03.066198+00:00
-- url     : https://prove2.me/submissions/dab25770-acbd-42f0-a924-b7bed6c3f922

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField

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
theorem _root_.solution (K : Type*) [Field K] (N : ℕ)
    (𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔐.IsMaximal] :
    𝔐.comap MvPolynomial.C = IsLocalRing.maximalIdeal K := by
  have h1 := (Ideal.eq_bot_or_top (𝔐.comap MvPolynomial.C)).resolve_right
    (inferInstance : (𝔐.comap (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)).IsPrime).ne_top
  have h2 := (Ideal.eq_bot_or_top (IsLocalRing.maximalIdeal K)).resolve_right
    (IsLocalRing.maximalIdeal.isMaximal K).ne_top
  rw [h1, h2]
end ReciprocityTheory.CA
