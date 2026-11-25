-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:20.605498+00:00
-- url     : https://prove2.me/submissions/0584e485-3d02-4713-b6b8-7a9295b76492

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_add_ringKrullDim_quotient_fintype
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_eq_of_mem_minimalPrimes_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_withBot_enat_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2
end ReciprocityTheory.AnForm.R
