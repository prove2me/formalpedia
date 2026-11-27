-- Prove2me | solution 1 for UpperTheory.norm_integers_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:35:38.927378+00:00
-- url     : https://prove2.me/submissions/af6ed667-2cba-4f17-a376-0e1b2c0e9f32

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormIntegersLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact (Nat.Prime l)] (e : K →+* PadicAlgCl l) (x : NumberField.RingOfIntegers K), ‖e (algebraMap (NumberField.RingOfIntegers K) K x)‖ ≤ 1 := by
  intro K _ _ l _ e x
  have hx : IsIntegral ℤ (e (algebraMap (NumberField.RingOfIntegers K) K x)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map e.toIntAlgHom
  generalize e (algebraMap (NumberField.RingOfIntegers K) K x) = y at hx
  let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
  have hS : IsIntegral S y := hx.tower_top
  have h := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral hS
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h
end UpperTheory
