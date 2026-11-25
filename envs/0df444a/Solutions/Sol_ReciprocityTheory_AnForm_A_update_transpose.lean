-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.update_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:53.909247+00:00
-- url     : https://prove2.me/submissions/c1154598-d20e-4241-98c0-3bb764a1d41f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    (fun r => (Function.update (Function.update A p X) q Y r)ᵀ) =
      Function.update (Function.update (fun r => (A r)ᵀ) p Xᵀ) q Yᵀ := by
  funext r
  simp only [Function.update_apply]
  split_ifs <;> rfl
end ReciprocityTheory.AnForm.A
