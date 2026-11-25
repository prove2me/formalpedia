-- Prove2me | solution 1 for PI.DivPowInteg.Gen.pow_apply_eq_zero_of_lowDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:40.663033+00:00
-- url     : https://prove2.me/submissions/b5f58e99-6d02-446c-9c4d-99ad11c4e659

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenVan
import Theorems.Thm_PI_DivPowInteg_Gen_eq_zero_of_mem_lowDeg_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K σ ι : Type} [CommRing K] [Fintype ι]
namespace PI.DivPowInteg.Gen
theorem _root_.solution (D : Module.End K (MvPolynomial σ K)) (f : ι → σ)
    (hD : ∀ t R, R ∈ lowDeg f (t + 1) → D R ∈ lowDeg f t) :
    ∀ n R, R ∈ lowDeg f n → (D ^ n) R = 0 := by
  intro n
  induction n with
  | zero =>
    intro R hR
    rw [pow_zero]
    exact eq_zero_of_mem_lowDeg_zero hR
  | succ n ih =>
    intro R hR
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hD n R hR)
end PI.DivPowInteg.Gen
