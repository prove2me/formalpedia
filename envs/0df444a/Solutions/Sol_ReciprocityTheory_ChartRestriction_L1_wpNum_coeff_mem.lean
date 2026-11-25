-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.wpNum_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:42.856725+00:00
-- url     : https://prove2.me/submissions/95dc37e6-6c2d-49f6-871f-99e5291c35e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPoly
import Theorems.Thm_Formalism_L2_Th1_A_seriesMap
import Theorems.Thm_Formalism_L2_Th1_F_seriesMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (k : Subfield ℂ) {g2 g3 : ℂ} (h2 : g2 ∈ k) (h3 : g3 ∈ k) (n : ℕ) :
    PowerSeries.coeff n (wpNum g2 g3) ∈ k := by
  have h := (seriesMap k ℂ k.subtype ⟨g2, h2⟩ ⟨g3, h3⟩ 0 0).1
  have h' : wpNum g2 g3 = PowerSeries.map k.subtype (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩) := h.symm
  rw [h', PowerSeries.coeff_map]
  exact (PowerSeries.coeff n (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩)).2
end ReciprocityTheory.ChartRestriction.L1
