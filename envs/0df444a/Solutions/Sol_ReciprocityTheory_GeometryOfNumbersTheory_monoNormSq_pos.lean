-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.monoNormSq_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:19.576509+00:00
-- url     : https://prove2.me/submissions/c4caa1f9-0332-4e72-8204-12dd757ebd41

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
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by
  unfold monoNormSq
  apply div_pos
  · apply mul_pos
    · exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos (a i))
    · exact_mod_cast Nat.factorial_pos D
  · exact_mod_cast Nat.factorial_pos _
end ReciprocityTheory.GeometryOfNumbersTheory
