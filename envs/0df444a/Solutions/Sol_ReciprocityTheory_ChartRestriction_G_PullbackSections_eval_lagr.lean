-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.eval_lagr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:08.820536+00:00
-- url     : https://prove2.me/submissions/68c82465-f709-4842-a1af-2fdff52c43d4

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
theorem _root_.solution (x : ι → K) (hx : Function.Injective x) (τ τ' : ι) :
    (lagr x τ).eval (x τ') = if τ = τ' then 1 else 0 := by
  unfold lagr
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self hx.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ _)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
