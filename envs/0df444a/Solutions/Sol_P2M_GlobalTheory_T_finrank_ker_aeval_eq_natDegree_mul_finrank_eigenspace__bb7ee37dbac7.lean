-- Prove2me | solution 1 for P2M_GlobalTheory_T_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace__bb7ee37dbac7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:07.184483+00:00
-- url     : https://prove2.me/submissions/a4984c7e-b498-414f-bb0c-a25c66f37153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement
import Theorems.Thm_GlobalTheory_finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  first | exact @GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace | exact GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace | (intros; apply GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace <;> assumption)
end _root_.GlobalTheory.T
