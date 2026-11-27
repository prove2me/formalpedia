-- Prove2me | solution 1 for P2M_GlobalTheory_T_linearIndependent_vecMul_of_span_rat__bc866713cde8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:11.086416+00:00
-- url     : https://prove2.me/submissions/85fb8e5e-cbaa-42df-b031-6bcbad063e83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentVecMulOfSpanRat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentVecMulOfSpanRatStatement
import Theorems.Thm_GlobalTheory_linearIndependent_vecMul_of_span_rat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  first | exact @GlobalTheory.linearIndependent_vecMul_of_span_rat | exact GlobalTheory.linearIndependent_vecMul_of_span_rat | (intros; apply GlobalTheory.linearIndependent_vecMul_of_span_rat <;> assumption)
end _root_.GlobalTheory.T
