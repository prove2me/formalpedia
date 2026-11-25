-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_card_filter_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:20.885265+00:00
-- url     : https://prove2.me/submissions/a8880ef9-d12f-4dbc-83b2-77975f2e388b

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
theorem _root_.solution (D n : ℕ) :
    ((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card ≤
      (Finset.Nat.antidiagonalTuple D (n + 1)).card := by
  apply Finset.card_le_card_of_injOn (fun b i => b i.succ)
  · intro b hb
    have h0 : b 0 = 0 := (Finset.mem_filter.mp hb).2
    have h1 := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1
    rw [Fin.sum_univ_succ, h0, zero_add] at h1
    exact Finset.Nat.mem_antidiagonalTuple.mpr h1
  · intro b hb c hc hbc
    have hb0 : b 0 = 0 := (Finset.mem_filter.mp hb).2
    have hc0 : c 0 = 0 := (Finset.mem_filter.mp hc).2
    funext j
    refine Fin.cases ?_ (fun i => congrFun hbc i) j
    rw [hb0, hc0]
end ReciprocityTheory.GeometryOfNumbersTheory
