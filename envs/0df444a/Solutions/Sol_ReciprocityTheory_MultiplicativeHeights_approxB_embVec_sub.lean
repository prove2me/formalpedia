-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_embVec_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:30.289383+00:00
-- url     : https://prove2.me/submissions/6ce4af44-0b00-4ea5-a72e-8b3bd0aac812

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB

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
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (x y : Fin r → K) : embVec σ (x - y) = embVec σ x - embVec σ y := by
  funext a
  simp [embVec]
end ReciprocityTheory.MultiplicativeHeights
