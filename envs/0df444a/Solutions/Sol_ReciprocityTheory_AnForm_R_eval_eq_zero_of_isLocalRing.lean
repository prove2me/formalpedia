-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.eval_eq_zero_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:12.153795+00:00
-- url     : https://prove2.me/submissions/20ecd58f-3652-4dcb-85f0-58730bfab6b2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] : ∀ k ∈ K, eval p k = 0 := by
  intro k hk
  by_contra hne
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) k) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) k).2 (fun h => hne (RingHom.mem_ker.1 h))
  have htop : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hk) hu
  have hs : Subsingleton (locRing K p) := Ideal.Quotient.subsingleton_iff.2 htop
  exact not_subsingleton (locRing K p) hs
end ReciprocityTheory.AnForm.R
