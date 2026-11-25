-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_lagr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:28:05.537868+00:00
-- url     : https://prove2.me/submissions/c0c138a3-a148-43d7-9ad0-b02242610b7c

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
theorem _root_.solution (x : ι → K) (hx : Function.Injective x) [Nonempty ι] : ∑ τ, lagr x τ = 1 :=
  Lagrange.sum_basis hx.injOn Finset.univ_nonempty
end ReciprocityTheory.ChartRestriction.G.PullbackSections
