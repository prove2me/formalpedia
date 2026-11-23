-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:34.348467+00:00
-- url     : https://prove2.me/submissions/8ed9a39d-1668-4027-ae80-1d93a2e3ff2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {ι : Type} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hermC_zero_left τ G v
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_left, ih]
end ReciprocityTheory.ChartRestriction.G.FD
