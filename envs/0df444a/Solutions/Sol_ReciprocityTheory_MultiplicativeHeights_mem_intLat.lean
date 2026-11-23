-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.mem_intLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:29.931433+00:00
-- url     : https://prove2.me/submissions/43a399e7-ad5c-45ec-8cd8-86abd0ec74eb

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (x : Fin r → K) :
    x ∈ intLat K r ↔ ∀ a, IsIntegralElt (x a) := by
  simp only [intLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  rfl
end ReciprocityTheory.MultiplicativeHeights
