-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__sum_98f4f63a0a11
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:32.393217+00:00
-- url     : https://prove2.me/submissions/93a053f8-b52e-463b-9a59-566c911abf5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAtHom_eb5802171cfc
import Theorems.Thm_P2M_GlobalTheory_valAt__of_not_le_8b0812974c03

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
variable {X Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (x : Sp ℂ ⟶ X) (U : X.Opens) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∑ i ∈ s, f i) = ∑ i ∈ s, valAt' x U (f i) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_sum]
  · simp only [valAt'_of_not_le x h, Finset.sum_const_zero]
end GlobalTheory
