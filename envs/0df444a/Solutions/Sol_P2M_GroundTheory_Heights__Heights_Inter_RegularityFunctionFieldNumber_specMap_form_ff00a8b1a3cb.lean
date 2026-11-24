-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_form_ff00a8b1a3cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:03.433889+00:00
-- url     : https://prove2.me/submissions/8190801d-a05c-4116-800f-ad6b022e8c4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_aeval_blockScale_int_a871d57ac8d9


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
open GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable [DecidableEq K] {E : Type*} [Field E]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
theorem _root_.solution (ψ : MRing ι →+* E) (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    specMap ψ S g = (∏ k, cS E S k ^ a k) * MvPolynomial.C (ψ g) := by
  have e : (aeval fun p => MvPolynomial.C (ψ (X p)) : MRing ι →ₐ[ℤ] MvPolynomial K E) =
      ((MvPolynomial.C : E →+* MvPolynomial K E).comp ψ).toIntAlgHom :=
    MvPolynomial.algHom_ext fun p => by rw [aeval_X]; rfl
  rw [specMap, regularityLocalResidue_holds.aeval_blockScale_int hg, e]
  rfl
end GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
