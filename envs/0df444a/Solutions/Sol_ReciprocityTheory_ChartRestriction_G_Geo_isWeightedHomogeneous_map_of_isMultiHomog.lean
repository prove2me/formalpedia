-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_map_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:35.823261+00:00
-- url     : https://prove2.me/submissions/954efed9-c18a-406c-b521-1e22f2772637

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blkW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) s) a := by
  intro d hd
  rw [coeff_map] at hd
  have hs' : d ∈ s.support := by
    rw [mem_support_iff]
    intro h0
    apply hd
    simp [h0]
  funext k
  rw [weight_blkW]
  exact hs d hs' k
end ReciprocityTheory.ChartRestriction.G.Geo
