-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:40.901224+00:00
-- url     : https://prove2.me/submissions/a177072b-76e5-41a6-bc6a-32a82cdaffd6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (s : S) : 0 ≤ addv L v (algebraMap S L s) := by
  by_cases hs : s = 0
  · subst hs
    simp
  have hx : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S L
    rw [h, map_zero]
  have hv : v.valuation L (algebraMap S L s) ≠ 0 := by simpa using hx
  rw [addv_apply v hx]
  have h1 := (log_le_log hv one_ne_zero).mpr (v.valuation_le_one s)
  rw [log_one] at h1
  have h2 : (0 : ℤ) ≤ -log (v.valuation L (algebraMap S L s)) := by omega
  exact_mod_cast h2
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
