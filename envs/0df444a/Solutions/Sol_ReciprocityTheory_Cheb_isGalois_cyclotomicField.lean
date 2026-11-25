-- Prove2me | solution 1 for ReciprocityTheory.Cheb.isGalois_cyclotomicField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:18.738905+00:00
-- url     : https://prove2.me/submissions/d8a19682-0e26-423a-a3b9-648aa9b0240b

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossGal
import Theorems.Thm_ReciprocityTheory_Cheb_cxgal_exists_sf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by
  obtain ⟨p, hp0, hp⟩ := cxgal_exists_sf K
  have : IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)
  have := IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0
    (X_pow_sub_C_ne_zero (NeZero.pos l) 1)
  have : Normal ℚ (CyclotomicField l K) := Normal.of_isSplittingField (p * (X ^ l - 1))
  exact IsGalois.mk
end ReciprocityTheory.Cheb
