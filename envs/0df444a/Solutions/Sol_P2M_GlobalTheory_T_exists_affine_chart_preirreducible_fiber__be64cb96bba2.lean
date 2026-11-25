-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_affine_chart_preirreducible_fiber__be64cb96bba2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:06:47.530306+00:00
-- url     : https://prove2.me/submissions/9e12685f-9694-4b91-832b-3ac41fafd8d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiberStatement
import Theorems.Thm_GlobalTheory_exists_affine_chart_preirreducible_fiber


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
theorem _root_.solution : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  first | exact @GlobalTheory.exists_affine_chart_preirreducible_fiber | exact GlobalTheory.exists_affine_chart_preirreducible_fiber | (intros; apply GlobalTheory.exists_affine_chart_preirreducible_fiber <;> assumption)
end _root_.GlobalTheory.T
