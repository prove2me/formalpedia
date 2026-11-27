-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.hasDerivAt_of_mulHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:24.858363+00:00
-- url     : https://prove2.me/submissions/943f911d-a3da-4264-9312-bdc56ba223b6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtOfContinuousHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WirtingerCombinationNeZero
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_ArchimedeanWhittakerDerivatives_HasDerivAtOfMulHom
import Theorems.Thm_GlobalTheory_CompanionTheory_CharDeriv_hasDerivAt_of_continuous_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) (hm : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t :=
  GlobalTheory.CompanionTheory.CharDeriv.hasDerivAt_of_continuous_hom χ hc h0 hm
end PositivityTheory.Rg.Cz
