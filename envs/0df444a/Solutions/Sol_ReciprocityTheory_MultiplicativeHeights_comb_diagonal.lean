-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.comb_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:27.552494+00:00
-- url     : https://prove2.me/submissions/1cfaa08b-eab9-40bd-b93c-fc08b84c7838

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB

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
open Matrix NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ} (v : Fin k → Fin r → K)
    (D : 𝓞 K) : (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • v i) = fun j => D • v j := by
  funext j
  simp [Matrix.diagonal_apply, ite_smul]
end ReciprocityTheory.MultiplicativeHeights
