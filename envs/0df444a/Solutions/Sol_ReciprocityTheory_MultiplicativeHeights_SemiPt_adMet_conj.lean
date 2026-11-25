-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.adMet_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:37.992095+00:00
-- url     : https://prove2.me/submissions/d1d6b281-9ca7-4016-9583-aa376b67152a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (σ : K →+* ℂ) :
    adMet r m g dd ((starRingEnd ℂ).comp σ) = adMet r m g dd σ := by
  funext i
  unfold adMet
  simp only [RingHom.comp_apply, Complex.norm_conj]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
