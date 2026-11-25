-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hypInclAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:28.680132+00:00
-- url     : https://prove2.me/submissions/15d07f9c-012b-4dde-b245-63beec59bf42

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (w : Fin n → ℂ) : hypInclAt 0 w = hypIncl w := by
  funext j
  simp [hypInclAt, hypIncl, Fin.insertNth_zero']
end ReciprocityTheory.AnForm.A
