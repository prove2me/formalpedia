-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.chartIdeal_le_ptIdealOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:41.911803+00:00
-- url     : https://prove2.me/submissions/323074d1-eae4-4eb8-ae5a-da49d90ada50

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart

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
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    chartIdeal P p ≤ ptIdealOf z := fun h hh => by
  show h ∈ RingHom.ker (MvPolynomial.eval z : MvPolynomial (Σ k, ι k) ℂ →+* ℂ)
  exact RingHom.mem_ker.2 (hz h hh)
end ReciprocityTheory.AnForm.R
