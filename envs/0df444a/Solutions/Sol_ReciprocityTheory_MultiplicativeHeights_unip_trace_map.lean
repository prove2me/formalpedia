-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_trace_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:52.263091+00:00
-- url     : https://prove2.me/submissions/d5ad9369-6e10-4fbe-9ad7-02bb323dc016

import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K) :
    (M.map σ).trace = σ M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
end ReciprocityTheory.MultiplicativeHeights
