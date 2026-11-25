-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PowerSumsEsymmAnalytic_proof_26eb33cc1ba6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:45.090333+00:00
-- url     : https://prove2.me/submissions/8500c3db-616c-4013-81a0-41a610951d33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPowerSumsEsymmAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_multiset_mul_esymm_eq_sum_1307572d2479

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Finset
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PowerSumsEsymmAnalytic
theorem _root_.solution : PowerSumsEsymmAnalytic.Statement := by
  intro σ _ V d Z hV hcard hp k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa [Multiset.esymm, Multiset.powersetCard_zero_left] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)) (s := V))
  by_cases hkd : d < k
  · refine (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))).congr hV fun z hz => ?_
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard z hz]; exact hkd)]
  push Not at hkd
  have hsum : AnalyticOnNhd ℂ (fun z => ((k : ℂ))⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (Z z).esymm a.1 * ((Z z).map fun x => x ^ a.2).sum)) V := by
    refine analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)
    refine Finset.analyticOnNhd_fun_sum _ fun a ha => ?_
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    refine (analyticOnNhd_const.mul (ih a.1 ha.2)).mul (hp a.2 (by omega) (by omega))
  refine hsum.congr hV fun z _ => ?_
  rw [← multiset_mul_esymm_eq_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]
end PowerSumsEsymmAnalytic
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
