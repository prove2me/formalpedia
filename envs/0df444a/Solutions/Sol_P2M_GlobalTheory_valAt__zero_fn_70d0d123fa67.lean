-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__zero_fn_70d0d123fa67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:54.371579+00:00
-- url     : https://prove2.me/submissions/b92ed4f5-057a-4220-9817-cac35922b319

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsAHOfPolarisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl
end GlobalTheory
