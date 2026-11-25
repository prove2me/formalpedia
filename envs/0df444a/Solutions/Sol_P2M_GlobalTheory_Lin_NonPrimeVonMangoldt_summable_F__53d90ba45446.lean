-- Prove2me | solution 1 for P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_summable_F__53d90ba45446
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:38.662131+00:00
-- url     : https://prove2.me/submissions/460b97d8-ec98-43c5-a6dc-d674456a0bb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Theorems.Thm_P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829
import Theorems.Thm_P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__le_6223be0b5b7b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.NonPrimeVonMangoldt
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
theorem _root_.solution : Summable F₂ := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4) : ℝ) := by positivity
  have hr1 : (2 : ℝ) ^ (-(3 / 4) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hA : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(5 / 4) : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hB := summable_geometric_of_lt_one hr0 hr1
  have hAB := Summable.mul_of_nonneg hA hB (fun p => by positivity) (fun k => by positivity)
  refine (hAB.mul_left 4).of_nonneg_of_le (fun pk => ?_) (fun pk => F₂_le pk.1 pk.2)
  obtain ⟨p, k⟩ := pk
  rw [F₂_eq]
  have := Real.log_natCast_nonneg (p : ℕ)
  positivity
end GlobalTheory.Lin.NonPrimeVonMangoldt
