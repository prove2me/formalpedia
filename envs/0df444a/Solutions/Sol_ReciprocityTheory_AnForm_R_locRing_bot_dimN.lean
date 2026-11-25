-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.locRing_bot_dimN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:39.022326+00:00
-- url     : https://prove2.me/submissions/c7be59b8-d031-4337-a77b-a02f73f990fe

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
import Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdeal_isMaximal
import Theorems.Thm_ReciprocityTheory_CA_height_maximal_mvPolynomial_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) = n := by
  have := ptIdeal_isMaximal p
  rw [← ringKrullDim_eq_of_ringEquiv (locRingBotEquivN p),
    IsLocalization.AtPrime.ringKrullDim_eq_height (ptIdeal p) (locPt p),
    (ReciprocityTheory.CA.height_maximal_mvPolynomial_field ℂ n (ptIdeal p)).2]
  rfl
end ReciprocityTheory.AnForm.R
