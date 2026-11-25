-- Prove2me | solution 1 for P2M_GlobalTheory_T_finiteDimensional_ker_aeval_of_eigenspaces__1c38240932a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:30.843677+00:00
-- url     : https://prove2.me/submissions/af0a9ccf-47a6-425c-be24-8ad217eb4de5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalKerAevalOfEigenspaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalKerAevalOfEigenspacesStatement
import Theorems.Thm_GlobalTheory_finiteDimensional_ker_aeval_of_eigenspaces


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M), (∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) → ∀ p : Polynomial ℂ, p ≠ 0 → FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  first | exact @GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | exact GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | (intros; apply GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces <;> assumption)
end _root_.GlobalTheory.T
