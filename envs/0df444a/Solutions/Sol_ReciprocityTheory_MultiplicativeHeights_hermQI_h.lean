-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.hermQI_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:07.222917+00:00
-- url     : https://prove2.me/submissions/0c9ab452-705c-445a-83e9-f02e5df51b7b

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (x y : Fin 1 → QI) :
    hermQI.h x y = IsCMField.complexConj QI (x 0) * y 0 := by
  simp [HermForm.h, hermQI]
end ReciprocityTheory.MultiplicativeHeights
