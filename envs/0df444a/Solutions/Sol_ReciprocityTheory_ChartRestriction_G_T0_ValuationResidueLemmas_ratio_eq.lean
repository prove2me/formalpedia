-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:52.522795+00:00
-- url     : https://prove2.me/submissions/d00ec481-f277-4c41-bf0b-7de8bb2c79a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (hf : f = a • g) : ratio f g = a := by
  unfold ratio
  have h : ∃ a : Ω, f = a • g := ⟨a, hf⟩
  rw [dif_pos h]
  exact smul_left_injective Ω hg (h.choose_spec.symm.trans hf)
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
