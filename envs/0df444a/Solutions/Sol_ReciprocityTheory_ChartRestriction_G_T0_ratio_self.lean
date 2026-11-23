-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ratio_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:05.853349+00:00
-- url     : https://prove2.me/submissions/3b85b26a-edd0-4278-ab64-d34c7752fa92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have h : ∃ a : Ω, f = a • f := ⟨1, (one_smul _ _).symm⟩
  rw [ratio, dif_pos h]
  have hc := h.choose_spec
  have h0 : (h.choose - 1) • f = 0 := by rw [sub_smul, ← hc, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hf
end ReciprocityTheory.ChartRestriction.G.T0
