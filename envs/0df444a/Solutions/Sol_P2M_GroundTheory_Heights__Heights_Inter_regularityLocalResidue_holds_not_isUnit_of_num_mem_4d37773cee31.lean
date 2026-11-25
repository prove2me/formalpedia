-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_not_isUnit_of_num_mem_4d37773cee31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:38.965993+00:00
-- url     : https://prove2.me/submissions/5f756d00-ee72-4695-9b19-548c8e4693f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_eq_zero_iff_cc85a26563f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P : Ideal (MRing ι))
variable {P} [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
theorem _root_.solution {W : Ideal (MRing ι)} (hW : W.IsPrime) (hPW : P ≤ W) {x : locRing P W}
    {u v : MRing ι} (hx : (x : FractionRing (MRing ι ⧸ P)) * frHom P v = frHom P u) (hu : u ∈ W) (hv : v ∉ W) :
    ¬ IsUnit x := by
  intro hxu
  obtain ⟨y, hy⟩ := hxu.exists_right_inv
  obtain ⟨u', v', a', -, -, hv', e'⟩ := exists_rep hW y.2
  have hxy : (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by
    rw [← Subring.coe_mul, hy, Subring.coe_one]
  have h1 : frHom P (u * u') = frHom P (v * v') := by
    rw [map_mul, map_mul, ← hx, ← e']
    calc _ = ((x : FractionRing (MRing ι ⧸ P)) * y) * (frHom P v * frHom P v') := by ring
      _ = _ := by rw [hxy, one_mul]
  have h2 : u * u' - v * v' ∈ P := by rw [← frHom_eq_zero_iff, map_sub, h1, sub_self]
  have h3 : v * v' ∈ W := by
    have := W.sub_mem (W.mul_mem_right u' hu) (hPW h2)
    rwa [sub_sub_cancel] at this
  exact (hW.mem_or_mem h3).elim hv hv'
end GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
