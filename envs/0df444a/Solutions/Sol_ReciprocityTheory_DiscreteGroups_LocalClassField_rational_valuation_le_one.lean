-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.rational_valuation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:12.801801+00:00
-- url     : https://prove2.me/submissions/7ab1e2af-cb08-4d6f-bd53-4162c175ba96

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_valuation_intCast_le_one_local_class_field

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
theorem _root_.solution (hp : valuation K (p : K) < 1) (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    valuation K (q : K) ≤ 1 := by
  rw [Rat.padicValuation_le_one_iff] at hq
  have hc : IsCoprime (p : ℤ) (q.den : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.2 (by
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq)
  obtain ⟨a, b, hab⟩ := hc
  have hden : 1 ≤ valuation K (q.den : K) := by
    by_contra hlt
    rw [not_le] at hlt
    have e : ((a : K) * (p : K) + (b : K) * (q.den : K)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
    have h1 : valuation K ((a : K) * (p : K)) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one_local_class_field a)) hp
    have h2 : valuation K ((b : K) * (q.den : K)) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_intCast_le_one_local_class_field b)) hlt
    have := (valuation K).map_add_lt h1 h2
    rw [e, map_one] at this
    exact lt_irrefl _ this
  rw [Rat.cast_def, map_div₀]
  have hpos : 0 < valuation K (q.den : K) := lt_of_lt_of_le zero_lt_one hden
  rw [div_le_one₀ hpos]
  exact (valuation_intCast_le_one_local_class_field q.num).trans hden
end ReciprocityTheory.DiscreteGroups.LocalClassField
