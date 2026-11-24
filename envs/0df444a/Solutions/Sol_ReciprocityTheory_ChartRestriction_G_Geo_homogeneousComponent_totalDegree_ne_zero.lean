-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.homogeneousComponent_totalDegree_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:04.214688+00:00
-- url     : https://prove2.me/submissions/ffca0ea9-aa3b-4dab-a073-2f34ea3c8dd3

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {σ : Type*} {F : MvPolynomial σ k} (hF : F ≠ 0) :
    homogeneousComponent F.totalDegree F ≠ 0 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun s => s.sum fun _ e => e)
  intro h0
  have := congrArg (coeff m) h0
  rw [coeff_homogeneousComponent, if_pos (by rw [totalDegree, hmax]; rfl), coeff_zero] at this
  exact (mem_support_iff.mp hm) this
end ReciprocityTheory.ChartRestriction.G.Geo
