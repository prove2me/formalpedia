-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:34.481794+00:00
-- url     : https://prove2.me/submissions/c2cb6c0a-1e69-4a42-818b-9715df7d6f18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} [Fact l.Prime] {z : ℂ_[l]} (hz : IsAlgebraic ℚ_[l] z) :
    ∃ y : PadicAlgCl l, algebraMap (PadicAlgCl l) ℂ_[l] y = z := by

  have hsplit : ((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).Splits :=
    IsAlgClosed.splits _
  have hne : (minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hz.isIntegral)
  have hroot : (((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).map
      (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot z := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact (Polynomial.eval_map_algebraMap _ _).trans (minpoly.aeval _ _)
  obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot hne hroot
  exact ⟨y, hy⟩
end ReciprocityTheory.ChartRestriction.L1
