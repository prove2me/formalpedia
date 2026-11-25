-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.prod_option_eq_prod_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:50.189808+00:00
-- url     : https://prove2.me/submissions/57c8a180-f1c8-4805-b765-3c2cdc6a0f3d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e r : ℕ} (σ : Fin r → Option (Fin e)) (m : Fin r → ℕ)
    (w : Fin e → ℂ) (g : Fin r → ℂ) (hg : ∀ k, g k = ∏ i, if σ k = some i then w i ^ m k else 1) :
    ∏ k, g k = ∏ i, w i ^ (((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ)) : ℤ) := by
  simp_rw [hg]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, zpow_natCast]
end ReciprocityTheory.AnForm.M
