-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.rational_valuation_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:33:06.582505+00:00
-- url     : https://prove2.me/submissions/84ddda07-57d9-43e3-8f9e-f552841976e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_rational_valuation_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hp : valuation K (p : K) < 1) (q : ℚ) (n : ℕ)
    (hq : Rat.padicValuation p q < Rat.padicValuation p ((p : ℚ) ^ n)) :
    valuation K (q : K) ≤ valuation K (p : K) ^ n := by
  have hp0 : ((p : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hpv : Rat.padicValuation p ((p : ℚ) ^ n) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact hp0
  have h1 : Rat.padicValuation p (q / (p : ℚ) ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.2 hpv)).2 hq |>.le
  have h2 := rational_valuation_le_one (K := K) p hp _ h1
  have hpF : ((p : K) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hvF : valuation K ((p : K) ^ n) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hpF
  push_cast at h2
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvF), map_pow] at h2
  exact h2
end ReciprocityTheory.DiscreteGroups.LocalClassField
