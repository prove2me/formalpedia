-- Prove2me | solution 1 for P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_summable_F__d163da7fbe74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:06.810241+00:00
-- url     : https://prove2.me/submissions/4bbdb233-508c-4659-a54a-24d95508f133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Theorems.Thm_P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_summable_F__53d90ba45446

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
open Nat.Primes
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
theorem _root_.solution : Summable F₀ := by
  have hF₀ (p : Nat.Primes) : F₀ p.val = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F₀]
  refine (summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr
      fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_
  swap
  · simp +contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn,
      not_false_eq_true, implies_true, true_or, F₀]
  have hFF' :
      F₀ ∘ Subtype.val (p := fun n ↦ n ∈ {n | IsPrimePow n}) = F₁ ∘ ⇑prodNatEquiv.symm := by
    refine (Equiv.eq_comp_symm prodNatEquiv (F₀ ∘ Subtype.val) F₁).mpr ?_
    ext1 n
    simp only [Function.comp_apply, F₁]
    congr
  rw [hFF']
  refine (Nat.Primes.prodNatEquiv.symm.summable_iff (f := F₁)).mpr ?_
  have hF'₀ (p : Nat.Primes) : F₁ (p, 0) = 0 := by simp only [zero_add, pow_one, hF₀, F₁]
  refine (Function.Injective.summable_iff (g := Prod.map _root_.id (· + 1)) ?_ fun u hu ↦ ?_).mp
    summable_F₂
  · exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1
  · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
      Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hF'₀ u.1, ← hu]
end GlobalTheory.Lin.NonPrimeVonMangoldt
