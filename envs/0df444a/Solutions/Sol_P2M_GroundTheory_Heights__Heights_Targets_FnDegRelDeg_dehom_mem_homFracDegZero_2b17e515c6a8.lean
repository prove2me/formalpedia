-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_dehom_mem_homFracDegZero_2b17e515c6a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:21.014601+00:00
-- url     : https://prove2.me/submissions/4b6c64e3-1b65-43b0-ae2b-38e3dce6016a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
theorem _root_.solution (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) (f : MRing ι F) :
    IntNumPoint.dehom V i f ∈ homFracDegZero V := by
  have : (IntNumPoint.dehom V i).range ≤ (homFracDegZero V).toSubalgebra := by
    rw [IntNumPoint.dehom, aeval_range]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin F _
      ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
        isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
  exact this ⟨f, rfl⟩
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
