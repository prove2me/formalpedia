-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_embVec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:18:27.437649+00:00
-- url     : https://prove2.me/submissions/5043f63d-01e4-4ad4-baea-ca30bb77b178

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
    (x y : Fin r → K) : embVec σ (x + y) = embVec σ x + embVec σ y := by
  funext a
  simp [embVec]
end ReciprocityTheory.MultiplicativeHeights
