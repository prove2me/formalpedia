-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:58.12581+00:00
-- url     : https://prove2.me/submissions/4cd220e4-3fb9-41b6-b3a6-56bdb6499aaf

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_eq_of_mem_minimalPrimes_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_add_ringKrullDim_quotient_fintype
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_withBot_enat_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have : Q.IsPrime := hQ.1.1
  have h1 := height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ] at h1
  exact withBot_enat_cancel h1 h2
end ReciprocityTheory.AnForm.R.BaseChangeC
