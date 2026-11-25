-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_embVec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:48.842874+00:00
-- url     : https://prove2.me/submissions/847a34ef-8dc5-43d2-a7e6-e8de5198f509

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
    (a : K) (x : Fin r → K) : embVec σ (a • x) = σ a • embVec σ x := by
  funext i
  simp [embVec]
end ReciprocityTheory.MultiplicativeHeights
