-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.wirtinger_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:46.208916+00:00
-- url     : https://prove2.me/submissions/43d8cabc-9066-43aa-94f6-b32c9a7afb8b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtOfContinuousHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WirtingerCombinationNeZero
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_ArchimedeanWhittakerDerivatives_HasDerivAtOfMulHom
import Theorems.Thm_GlobalTheory_CompanionTheory_Unitary_wirtinger_combination_ne_zero


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
theorem _root_.solution (χ : ℂ → ℂ) (hc : Continuous χ) (hm : ∀ z w, χ (z + w) = χ z * χ w) (hn : ∀ z, ‖χ z‖ = 1)
    (ht : ∃ z, χ z ≠ 1) (D : ℂ → ℂ) (hD : ∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) (β : ℂ) (hβ : β ≠ 0) :
    D β - Complex.I * D (β * Complex.I) ≠ 0 :=
  GlobalTheory.CompanionTheory.Unitary.wirtinger_combination_ne_zero χ hc hm hn ht D hD β hβ
end PositivityTheory.Rg.Cz
