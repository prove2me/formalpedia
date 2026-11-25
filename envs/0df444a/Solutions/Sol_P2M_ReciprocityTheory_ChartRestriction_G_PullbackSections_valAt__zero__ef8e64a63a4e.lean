-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__zero__ef8e64a63a4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:09.060092+00:00
-- url     : https://prove2.me/submissions/2cd9c091-532f-4435-b794-c5ffacdd656c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
