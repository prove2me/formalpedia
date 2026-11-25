-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_gramC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:48.527628+00:00
-- url     : https://prove2.me/submissions/e3240c00-7e3f-4e0b-a75d-4abe3a584634

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_gramX_eq

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
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embM σ b)ᴴ * H * embM σ b := sdd_gramX_eq H σ b b
end ReciprocityTheory.MultiplicativeHeights
