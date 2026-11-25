-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_low_coeff_not_dvd_of_congr_mul__eb8d4b502871
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:37.915602+00:00
-- url     : https://prove2.me/submissions/1fab1095-ea41-4582-be4f-f8e55f273143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLowCoeffNotDvdOfCongrMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLowCoeffNotDvdOfCongrMulStatement
import Theorems.Thm_GlobalTheory_exists_low_coeff_not_dvd_of_congr_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  first | exact @GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul | exact GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul | (intros; apply GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul <;> assumption)
end _root_.GlobalTheory.T
