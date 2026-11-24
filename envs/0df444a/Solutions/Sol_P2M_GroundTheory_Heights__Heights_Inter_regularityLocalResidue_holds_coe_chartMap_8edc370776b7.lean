-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_coe_chartMap_8edc370776b7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:37.210721+00:00
-- url     : https://prove2.me/submissions/8e4123fd-5d2a-427c-ad07-55acf4b4e929

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem

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
theorem _root_.solution {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k} (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W)
    (f : MRing ι) : (chartMap hPW T hT f : FractionRing (MRing ι ⧸ P)) =
      aeval (fun p => (frHom P (X ⟨p.1, T p.1⟩))⁻¹ * frHom P (X p)) f := by
  have e : (locRing P W).subtype.comp (chartMap hPW T hT) =
      (aeval (fun p => (frHom P (X ⟨p.1, T p.1⟩))⁻¹ * frHom P (X p)) :
        MRing ι →ₐ[ℤ] FractionRing (MRing ι ⧸ P)).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by
      simp [chartMap, mul_comm]
  exact DFunLike.congr_fun e f
end GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
