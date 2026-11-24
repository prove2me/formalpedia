-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_card_adt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:22.57082+00:00
-- url     : https://prove2.me/submissions/829a8bef-2a3c-4749-86c3-09058097fc88

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (k m : ℕ) : (Finset.Nat.antidiagonalTuple (k + 1) m).card ≤ (m + 1) ^ k := by
  calc (Finset.Nat.antidiagonalTuple (k + 1) m).card
      ≤ (Fintype.piFinset fun _ : Fin k => Finset.range (m + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun b i => b i.succ)
        · intro b hb
          have hb' := Finset.Nat.mem_antidiagonalTuple.mp hb
          simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
          intro i
          have : b i.succ ≤ ∑ j, b j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ _)
          omega
        · intro b hb c hc hbc
          have hb' := Finset.Nat.mem_antidiagonalTuple.mp hb
          have hc' := Finset.Nat.mem_antidiagonalTuple.mp hc
          have hs : ∀ i : Fin k, b i.succ = c i.succ := fun i => congrFun hbc i
          rw [Fin.sum_univ_succ] at hb' hc'
          have hsum : ∑ i : Fin k, b i.succ = ∑ i : Fin k, c i.succ :=
            Finset.sum_congr rfl (fun i _ => hs i)
          funext j
          refine Fin.cases ?_ (fun i => hs i) j
          omega
    _ = (m + 1) ^ k := by simp
end ReciprocityTheory.GeometryOfNumbersTheory
