-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_surjective_pi_adjoinRoot_ker_eq_range__b115a80cc821
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:18.79672+00:00
-- url     : https://prove2.me/submissions/6dceb38a-752f-4447-b035-927512bc8b1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Theorems.Thm_GlobalTheory_exists_surjective_pi_adjoinRoot_ker_eq_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) [Fact (Irreducible f)], ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧ (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧ LinearMap.ker π = LinearMap.range (aeval g f) ∧ Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  first | exact @GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range | exact GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range | (intros; apply GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range <;> assumption)
end _root_.GlobalTheory.T
