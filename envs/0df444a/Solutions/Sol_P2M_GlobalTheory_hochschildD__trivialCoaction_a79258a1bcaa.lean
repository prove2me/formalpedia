-- Prove2me | solution 1 for P2M_GlobalTheory_hochschildD__trivialCoaction_a79258a1bcaa
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:16:57.801373+00:00
-- url     : https://prove2.me/submissions/ac080006-3da0-433f-ab2f-ba9de339cf04

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
theorem _root_.solution : hochschildD₁ (trivialCoaction R H M) =
    (TensorProduct.mk R H H 1).lTensor M - (comul (R := R)).lTensor M +
      ((TensorProduct.mk R H H).flip 1).lTensor M := by
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
    | (intros; simp [hochschildD₁, trivialCoaction]; done)
    | (intros; grind)
    | (intros; grind [hochschildD₁, trivialCoaction])
    | (intros; unfold hochschildD₁ trivialCoaction; grind)
    | (intros; simp only [hochschildD₁, trivialCoaction] at * <;> grind)
    | (intros; simp_all [hochschildD₁, trivialCoaction] <;> grind)
    | (intros; ext <;> grind [hochschildD₁, trivialCoaction])
    | (intros; constructor <;> intro _ <;> grind [hochschildD₁, trivialCoaction])
    | (intro x; cases x <;> grind [hochschildD₁, trivialCoaction])
    | (intro x; induction x <;> simp_all [hochschildD₁, trivialCoaction])
    | (intro x y; induction x <;> grind [hochschildD₁, trivialCoaction])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [hochschildD₁, trivialCoaction])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [hochschildD₁, trivialCoaction])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_10_2"



