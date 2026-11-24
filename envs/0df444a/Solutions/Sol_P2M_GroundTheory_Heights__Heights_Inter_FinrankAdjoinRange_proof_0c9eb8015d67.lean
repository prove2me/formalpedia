-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FinrankAdjoinRange_proof_0c9eb8015d67
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:02.40081+00:00
-- url     : https://prove2.me/submissions/66a37a31-319d-45db-bbfe-e387b811887e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace FinrankAdjoinRange
theorem _root_.solution : FinrankAdjoinRange.Statement := by
  intro F Φ Ω _ _ _ _ _ _ _ S
  set f := IsScalarTower.toAlgHom F Φ Ω
  set Φ₁ : IntermediateField F Ω := f.fieldRange
  let i : Φ ≃ₐ[F] Φ₁ := AlgEquiv.ofInjectiveField f
  have hi : (algebraMap Φ Ω : Φ → Ω) = (algebraMap Φ₁ Ω) ∘ i := by
    funext x; rfl

  have hres : (IntermediateField.adjoin Φ S).restrictScalars F =
      (IntermediateField.adjoin Φ₁ S).restrictScalars F :=
    IntermediateField.restrictScalars_adjoin_of_algEquiv i hi S

  have hle : Φ₁ ≤ Φ₁ ⊔ IntermediateField.adjoin F S := le_sup_left
  have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin Φ₁ S := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup]
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]

  let j : IntermediateField.adjoin Φ S ≃+* IntermediateField.adjoin Φ₁ S :=
    (IntermediateField.equivOfEq hres).toRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv j ?_
  ext x
  rfl
end FinrankAdjoinRange
end GroundTheory.Heights₂.Heights.Inter
