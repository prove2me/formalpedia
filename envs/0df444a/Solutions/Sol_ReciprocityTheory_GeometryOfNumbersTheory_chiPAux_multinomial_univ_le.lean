-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_multinomial_univ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:30.493421+00:00
-- url     : https://prove2.me/submissions/dec95ae1-e953-4a94-90b6-bfc47f9dcc72

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
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) :
    Nat.multinomial Finset.univ a ≤ (D + 1) ^ (∑ i, a i) := by
  have key := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin (D + 1))) (fun _ => (1 : ℕ)) (∑ i, a i)
  simp only [one_pow, Finset.prod_const_one, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at key
  rw [key]
  apply Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)
  rw [Finset.mem_piAntidiag]
  exact ⟨rfl, fun i _ => Finset.mem_univ i⟩
end ReciprocityTheory.GeometryOfNumbersTheory
