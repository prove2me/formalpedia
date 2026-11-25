-- Prove2me | solution 1 for P2M_GlobalTheory_slices_test__ca01e1ad2132
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:35.751529+00:00
-- url     : https://prove2.me/submissions/4f0b6cb9-110b-4740-ac9d-a187d4c315ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyConstantCompactSupportSlicesOperatorApply
import Theorems.Thm_GlobalTheory_slices_test

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) :=
  fun T hT hT0 f hf => slices_test T hT hT0 f hf
end GlobalTheory
