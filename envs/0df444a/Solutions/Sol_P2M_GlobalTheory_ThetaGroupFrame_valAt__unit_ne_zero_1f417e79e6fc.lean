-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:54.763882+00:00
-- url     : https://prove2.me/submissions/0a90826b-1f05-49b2-9205-4997852af873

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution (hv : ValLaws) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he]
  intro h0
  have h1 := congrArg e s.mul_inv
  rw [map_mul, map_one, h0, zero_mul] at h1
  exact zero_ne_one h1
end GlobalTheory.ThetaGroupFrame
