-- Prove2me | solution 1 for ReciprocityTheory.CA.height_add_height_map_eq_mvPolynomial_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:44.773864+00:00
-- url     : https://prove2.me/submissions/69518900-e9f9-4e99-9bf4-4c95d45040ef

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_height_maximal_mvPolynomial_field
import Theorems.Thm_ReciprocityTheory_CA_height_eq_add_of_isCM_localization


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
    (𝔔 𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime] [𝔐.IsMaximal] (hle : 𝔔 ≤ 𝔐) :
    𝔔.height + (𝔐.map (Ideal.Quotient.mk 𝔔)).height = N := by
  obtain ⟨hcm, hh⟩ := height_maximal_mvPolynomial_field K N 𝔐
  rw [← hh]
  exact (height_eq_add_of_isCM_localization 𝔐 𝔔 hcm hle).symm
end ReciprocityTheory.CA
