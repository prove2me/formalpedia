-- Prove2me | solution 1 for UpperTheory.invOfUnit_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:48.864234+00:00
-- url     : https://prove2.me/submissions/195daca8-2d47-4d3d-86f3-9ec022da886c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvOfUnitCoeffMem

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
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
end UpperTheory
