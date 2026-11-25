-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_chartMap_form_f055cef6c4da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:03.74567+00:00
-- url     : https://prove2.me/submissions/4c73956c-4447-4fbd-8400-31ecbff42ec7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_aeval_blockScale_int_a871d57ac8d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_coe_chartMap_8edc370776b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_frHom_X_ne_zero_1717d23a360b

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
theorem _root_.solution {W : Ideal (MRing ι)} (hPW : P ≤ W) {T : ∀ k, ι k}
    (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    (chartMap hPW T hT f : FractionRing (MRing ι ⧸ P)) * frHom P (∏ k, (X ⟨k, T k⟩ : MRing ι) ^ a k) =
      frHom P f := by
  have hz : (aeval fun p => frHom P (X p) : MRing ι →ₐ[ℤ] FractionRing (MRing ι ⧸ P)).toRingHom = frHom P :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
  have hz' : (aeval fun p => frHom P (X p) : MRing ι →ₐ[ℤ] FractionRing (MRing ι ⧸ P)) f = frHom P f :=
    DFunLike.congr_fun hz f
  rw [coe_chartMap, aeval_blockScale_int hf (fun k => (frHom P (X ⟨k, T k⟩))⁻¹) (fun p => frHom P (X p)), hz', map_prod, mul_comm, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  simp_rw [map_pow, ← mul_pow, mul_inv_cancel₀ (frHom_X_ne_zero hPW hT _), one_pow, Finset.prod_const_one,
    one_mul]
end GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
