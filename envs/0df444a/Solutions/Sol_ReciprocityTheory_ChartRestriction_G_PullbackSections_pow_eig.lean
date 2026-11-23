-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.pow_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:14.961487+00:00
-- url     : https://prove2.me/submissions/4ed469e3-bb64-497e-9583-879aefbe3dcc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB

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
theorem _root_.solution (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (n : ℕ) : (f ^ n) m = x ^ n • m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hm, smul_smul, pow_succ]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
