-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isWeightedHomogeneous_of_isMultiHomog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:05.515923+00:00
-- url     : https://prove2.me/submissions/a2ee825a-9bc6-4ce9-866f-299a886c597c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blockWeight

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution [DecidableEq K] {s : MRing ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (blockWeight (ι := ι) k) s (a k) := by
  intro d hd
  rw [weight_blockWeight]
  exact h d (mem_support_iff.mpr hd) k
end ReciprocityTheory.ChartRestriction.G.Geo
