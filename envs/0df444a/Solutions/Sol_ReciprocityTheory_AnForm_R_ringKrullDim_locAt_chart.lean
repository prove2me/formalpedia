-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:43:07.860736+00:00
-- url     : https://prove2.me/submissions/c9875bb5-66ec-4117-ae9b-a0af79e1966e

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locAt_chart_le
import Theorems.Thm_ReciprocityTheory_AnForm_R_le_ringKrullDim_locAt_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P)
    (e : ℕ) (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    ringKrullDim (locAt (chartIdeal P p) z) = e :=
  le_antisymm (ringKrullDim_locAt_chart_le hP e hdim p z hz) (le_ringKrullDim_locAt_chart e hdim p z hz)
end ReciprocityTheory.AnForm.R
