-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:51.0668+00:00
-- url     : https://prove2.me/submissions/a65c75b6-01f5-4a88-a3e8-116732c95453

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
theorem _root_.solution (s : S) : 0 < addv L v (algebraMap S L s) ↔ s ∈ v.asIdeal := by
  by_cases hs : s = 0
  · subst hs
    rw [map_zero, AddValuation.map_zero]
    exact iff_of_true (WithTop.coe_lt_top 0) (Submodule.zero_mem _)
  have hx : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    apply IsFractionRing.injective S L
    rw [h, map_zero]
  have hv : v.valuation L (algebraMap S L s) ≠ 0 := by simpa using hx
  rw [addv_apply v hx, ← v.valuation_lt_one_iff_mem (K := L) s]
  have h1 : v.valuation L (algebraMap S L s) < 1 ↔
      ¬ (log (1 : WithZero (Multiplicative ℤ)) ≤ log (v.valuation L (algebraMap S L s))) := by
    rw [log_le_log one_ne_zero hv, not_le]
  rw [h1, log_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  constructor <;> intro h <;> omega
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
