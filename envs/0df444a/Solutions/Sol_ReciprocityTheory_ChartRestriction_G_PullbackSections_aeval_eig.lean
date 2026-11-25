-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.aeval_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:55.321222+00:00
-- url     : https://prove2.me/submissions/69d9a947-4331-4abf-a6ce-e14f06f84a39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_pow_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (P : ℤ[X]) :
    aeval f P m = aeval x P • m := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, pow_eig f hm, smul_assoc]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
