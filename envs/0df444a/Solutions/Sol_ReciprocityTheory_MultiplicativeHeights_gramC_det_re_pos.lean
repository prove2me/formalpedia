-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gramC_det_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:12.361878+00:00
-- url     : https://prove2.me/submissions/35ff0aed-82a2-4fb6-8541-728c12bedf62

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_posDef

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hH : H.PosDef) (hb : LinearIndependent K b) : 0 < (gramC H σ b).det.re := by
  classical
  exact (Complex.pos_iff.mp (gramC_posDef H σ b hH hb).det_pos).1
end ReciprocityTheory.MultiplicativeHeights
