-- Prove2me | solution 1 for P2M_GlobalTheory_T_preirreducibleSpace_tensor_of_pullback__31b77ef02540
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:33:54.074578+00:00
-- url     : https://prove2.me/submissions/eeaf851b-e7d6-4f07-b0f8-aec5de38ee44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullbackStatement
import Theorems.Thm_GlobalTheory_preirreducibleSpace_tensor_of_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k] [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom → PreirreducibleSpace ↥(pullback (W.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  first | exact @GlobalTheory.preirreducibleSpace_tensor_of_pullback | exact GlobalTheory.preirreducibleSpace_tensor_of_pullback | (intros; apply GlobalTheory.preirreducibleSpace_tensor_of_pullback <;> assumption)
end _root_.GlobalTheory.T
