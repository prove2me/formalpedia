-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegralElem_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:47.758779+00:00
-- url     : https://prove2.me/submissions/fab99573-3521-4dc5-bf6e-61871b0b4319

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (val : S →+* T) (hval : Function.Injective val) {s : S}
    (h : (val.comp f).IsIntegralElem (val s)) : f.IsIntegralElem s := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, hval ?_⟩
  rw [map_zero, ← he, Polynomial.hom_eval₂]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
