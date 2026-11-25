-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.locRing_bot_regularN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:16.864816+00:00
-- url     : https://prove2.me/submissions/f6de67d0-8677-4852-82f5-9c855a5b1372

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineMultihomogClassify
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv


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
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) :=
  IsRegularLocalRing.of_ringEquiv (locRingBotEquivN p)
end ReciprocityTheory.AnForm.R
