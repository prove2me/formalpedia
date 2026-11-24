-- Prove2me | solution 1 for TaoFivePrimes.theorem51_vaughan_split_centred_assembly
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-21T11:46:42.917255+00:00
-- url     : https://prove2.me/submissions/670237ba-2400-442a-89d0-71785a22118f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
import Theorems.Thm_TaoFivePrimes_smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
import Theorems.Thm_TaoFivePrimes_eta0VaughanTypeISum_le_theorem51TypeI

set_option autoImplicit false

/-! The centred Vaughan assembly: the conjunction of the two facts that
    remain for the centred Vaughan split `theorem51_vaughan_split` —
    (i) the centred decomposition identity (Proved on the platform) and
    (ii) the Type I envelope comparison (Open on the platform). Each
    conjunct is discharged by the corresponding imported platform
    theorem; the two statements agree up to elaboration of the ℤ/ℝ→ℂ
    coercions, which elaborate to identical terms. -/

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha =
      TaoFivePrimes.eta0VaughanTypeISum x alpha U V +
      ∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          (ArithmeticFunction.moebius d : ℂ) * (TaoFivePrimes.theorem51Centered V w : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) * (TaoFivePrimes.eta0 ((d : ℝ) * w / x) : ℂ)
        else 0)) ∧
    (∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c) := by
  refine ⟨?_, ?_⟩
  · exact TaoFivePrimes.smoothedExpSum_eq_eta0VaughanTypeISum_add_centredPairSum
      x alpha U V hU hV hUx hVx hUVx hUV2
  · exact TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI
      x alpha U V hU hV hUx hVx hUVx hUV2
