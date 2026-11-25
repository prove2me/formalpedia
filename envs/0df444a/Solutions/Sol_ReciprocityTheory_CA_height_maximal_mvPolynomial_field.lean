-- Prove2me | solution 1 for ReciprocityTheory.CA.height_maximal_mvPolynomial_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:13.276114+00:00
-- url     : https://prove2.me/submissions/2b3eaef1-a7f1-4b9d-add3-4299ecb1ca78

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_isCM_field
import Theorems.Thm_ReciprocityTheory_CA_comap_C_eq_maximalIdeal_field
import Theorems.Thm_ReciprocityTheory_CA_isCM_localization_mvPolynomial


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
    IsCM (Localization.AtPrime 𝔐) ∧ 𝔐.height = N := by
  obtain ⟨hcm, hh⟩ := isCM_localization_mvPolynomial (isCM_field K) N 𝔐
    (comap_C_eq_maximalIdeal_field K N 𝔐)
  refine ⟨hcm, ?_⟩
  rw [ringKrullDim_eq_zero_of_field K, zero_add] at hh
  exact_mod_cast hh
end ReciprocityTheory.CA
