-- Prove2me | solution 1 for UpperTheory.Top.PairGood.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:11.7128+00:00
-- url     : https://prove2.me/submissions/014e04cd-a858-46c4-bb01-abfeffa39897

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_PairGood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.Top
open Formalism.HC
namespace UpperTheory.Top
namespace PairGood
theorem _root_.solution {M : ℕ} {eps Y X X' : ℝ} {q d : ℕ} (h : PairGood M eps Y X q d) (hX : X' ≤ X) : PairGood M eps Y X' q d :=
  ⟨h.pair, h.coprime, fun ξ i j hij N _ χ hχ y a b => h.bounds ξ i j hij N χ hχ y a (b.trans hX), h.boxes⟩
end PairGood
end UpperTheory.Top
