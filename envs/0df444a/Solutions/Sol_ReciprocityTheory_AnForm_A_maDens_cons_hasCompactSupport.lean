-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_cons_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:29.576814+00:00
-- url     : https://prove2.me/submissions/936dbc1e-de0f-49e2-a604-0723114fe76a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {f : (Fin (n + 1) → ℂ) → ℝ} (hf : HasCompactSupport f)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : HasCompactSupport (maDens (Fin.cons f φ)) := by
  refine HasCompactSupport.intro hf.isCompact fun z hz => maDens_cons_eq_zero φ hz
end ReciprocityTheory.AnForm.A
