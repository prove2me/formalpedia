-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.colMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:43.052201+00:00
-- url     : https://prove2.me/submissions/055ad393-2bf9-4f3d-8f3a-adaa04c967fa

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    colMat b *ᵥ t = ∑ j, t j • b j := by
  funext a
  simp [colMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
