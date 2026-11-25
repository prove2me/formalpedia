-- Prove2me | solution 1 for ReciprocityTheory.AnForm.maDens_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:59.288714+00:00
-- url     : https://prove2.me/submissions/a8f41712-9fc0-4cab-bc49-46026aa4655b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) :
    maDens φ z = 2 / Real.pi * levi (φ 0) z (Pi.single 0 1) := by
  have hS : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp only [maDens, mdisc, hS]
  rw [Finset.sum_pair (by decide)]
  simp [hessC, levi, Matrix.det_unique]
end ReciprocityTheory.AnForm
