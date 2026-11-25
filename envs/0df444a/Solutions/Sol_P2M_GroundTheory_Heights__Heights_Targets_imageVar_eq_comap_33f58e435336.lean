-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_imageVar_eq_comap_33f58e435336
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:45.748873+00:00
-- url     : https://prove2.me/submissions/4c963607-7055-4968-be31-7ec8b052bf62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {F : Type u} [Field F] (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (V' : Ideal (MRing ι' F)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar F v V' =
      (contractPrime ⟨κ, hb.1⟩ V').comap (rename (blockVarEquiv hb)) := by
  ext f
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar contractPrime
  simp only [Ideal.mem_comap]
  have hfun : (blockIncl ⟨κ, hb.1⟩ ι' ∘ blockVarEquiv hb) = v := funext (blockIncl_blockVar hb)
  have e : rename (blockIncl ⟨κ, hb.1⟩ ι') (rename (blockVarEquiv hb) f) = rename v f := by
    rw [rename_rename, hfun]
  exact iff_of_eq (congrArg (· ∈ V') e.symm)
end GroundTheory.Heights₂.Heights.Targets
