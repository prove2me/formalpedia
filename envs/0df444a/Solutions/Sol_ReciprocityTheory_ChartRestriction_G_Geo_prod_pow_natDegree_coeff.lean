-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.prod_pow_natDegree_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:25.410484+00:00
-- url     : https://prove2.me/submissions/ad177d6c-4458-447e-94b6-037fa42600e0

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
import Theorems.Thm_Bl_FirstBlockLemmaA_goal1
import Theorems.Thm_Bl_general_b_fact_more_goal1


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
theorem _root_.solution {R ι : Type*} [CommRing R] (s : Finset ι) (p : ι → Polynomial R)
    (e : ι → ℕ) (hp : ∀ i, (p i).natDegree ≤ 1) :
    (∏ i ∈ s, p i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, p i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff 1 ^ e i := by
  first | exact Bl.general_b_fact_more.goal1 .. | (apply Bl.general_b_fact_more.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_more.goal1 <;> assumption)
end ReciprocityTheory.ChartRestriction.G.Geo
