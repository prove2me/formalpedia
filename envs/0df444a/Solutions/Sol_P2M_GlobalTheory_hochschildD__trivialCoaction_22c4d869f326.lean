-- Prove2me | solution 1 for P2M_GlobalTheory_hochschildD__trivialCoaction_22c4d869f326
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:16:56.297541+00:00
-- url     : https://prove2.me/submissions/57c9d6ff-bb9b-48e2-aac3-a54314efdef7

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Mathlib
import Mathlib.Tactic





-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]
theorem _root_.solution : hochschildD₂ (trivialCoaction R H M) =
    (TensorProduct.mk R H (H ⊗[R] H) 1).lTensor M -
      ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
      ((comul (R := R)).lTensor H).lTensor M -
      (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp [hochschildD₂, trivialCoaction]; done)
    | (intros; grind)
    | (intros; grind [hochschildD₂, trivialCoaction])
    | (intros; unfold hochschildD₂ trivialCoaction; grind)
    | (intros; simp only [hochschildD₂, trivialCoaction] at * <;> grind)
    | (intros; simp_all [hochschildD₂, trivialCoaction] <;> grind)
    | (intros; ext <;> grind [hochschildD₂, trivialCoaction])
    | (intros; constructor <;> intro _ <;> grind [hochschildD₂, trivialCoaction])
    | (intro x; cases x <;> grind [hochschildD₂, trivialCoaction])
    | (intro x; induction x <;> simp_all [hochschildD₂, trivialCoaction])
    | (intro x y; induction x <;> grind [hochschildD₂, trivialCoaction])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [hochschildD₂, trivialCoaction])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [hochschildD₂, trivialCoaction])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_10_0"



