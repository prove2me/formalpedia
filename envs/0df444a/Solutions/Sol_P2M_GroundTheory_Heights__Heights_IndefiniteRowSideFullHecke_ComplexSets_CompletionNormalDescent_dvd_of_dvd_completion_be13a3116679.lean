-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_dvd_of_dvd_completion_be13a3116679
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:31.376819+00:00
-- url     : https://prove2.me/submissions/62587938-56f8-448f-afef-4a1bb97465d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCompletionNormalDescent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open AdicCompletion Polynomial
variable {R : Type} [CommRing R] (J : Ideal R)
variable [IsNoetherianRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CompletionNormalDescent
theorem _root_.solution (hJ : J ≤ (⊥ : Ideal R).jacobson) (a b : R)
    (x : AdicCompletion J R)
    (h : algebraMap R (AdicCompletion J R) a = algebraMap R (AdicCompletion J R) b * x) : b ∣ a := by
  have H : IsHausdorff J (R ⧸ Ideal.span {b}) := IsHausdorff.of_le_jacobson J _ hJ
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
  have h1 := congrArg (evalₐ J n) h
  rw [map_mul, CompletionNormalDescent.evalₐ_algebraMap, CompletionNormalDescent.evalₐ_algebraMap, ← hr,
    ← map_mul, Ideal.Quotient.eq] at h1
  have h2 : Ideal.Quotient.mk (Ideal.span {b}) a = Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) := by
    rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b), zero_mul,
      sub_zero]
  have h3 : Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) =
      (a - b * r) • (Ideal.Quotient.mk (Ideal.span {b}) 1) := by
    rw [Algebra.smul_def, _root_.map_one, mul_one]
    rfl
  rw [h2, h3]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top
end CompletionNormalDescent
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
