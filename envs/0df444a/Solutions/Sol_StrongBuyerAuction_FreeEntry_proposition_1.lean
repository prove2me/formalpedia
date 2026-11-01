-- Prove2me | solution 1 for StrongBuyerAuction.FreeEntry.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:01:48.152979+00:00
-- url     : https://prove2.me/submissions/482f0d2f-f47e-40d5-bfee-58753cffbf39

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model
import Theorems.Thm_StrongBuyerAuction_FreeEntry_lemma_2
import Theorems.Thm_StrongBuyerAuction_FreeEntry_revenue_increasing_to_NG

open MeasureTheory ProbabilityTheory

open StrongBuyerAuction.FreeEntry in
theorem solution (μF μG μG' : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG) (hμG' : IsValueLaw μG')
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hG'G : FOSD (cdf μG') (cdf μG))
    (hguard : StrictWhereOpen (cdf μF) (cdf μG') (cdf μG))
    (NG NG' : ℝ)
    (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG)
    (hNG' : IsFreeEntry (cdf μF) (cdf μG') c NG') :
    rev (cdf μF) (cdf μG') NG' < rev (cdf μF) (cdf μG) NG := by
  -- Lemma 2: entry falls, N_{G'} < N_G
  have hlt := lemma_2 μF μG μG' hμF hμG hμG' c hc hGF hG'G hguard NG NG' hNG hNG'
  -- the guard set lies inside the nondegeneracy set (G > G' ≥ 0 there)
  have hnd : ProfitNondegenerate (cdf μF) (cdf μG) := by
    refine lt_of_lt_of_le hguard (measure_mono ?_)
    rintro x ⟨hx, h1, h2⟩
    exact ⟨hx, lt_of_le_of_lt (cdf_nonneg μG' x) h1, h2⟩
  -- with c frozen, revenue is strictly increasing on [1, N_G]
  have hmono := revenue_increasing_to_NG μF μG hμF hμG c hc hGF hnd NG hNG
  have key := hmono ⟨hNG'.2, hlt.le⟩ ⟨hNG.2, le_refl _⟩ hlt
  simp only at key
  unfold rev
  rw [hNG.1, hNG'.1]
  exact key
