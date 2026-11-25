-- Prove2me | solution 1 for P2M_GlobalTheory_T_natDegree_mul_esymm_roots_pow__380b48c19997
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:28.159278+00:00
-- url     : https://prove2.me/submissions/e22cbd41-0be4-4768-8c07-3def8216803b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPowStatement
import Theorems.Thm_GlobalTheory_CuspGL_natDegree_mul_esymm_roots_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  first | exact @GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow | exact GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow | (intros; apply GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow <;> assumption)
end _root_.GlobalTheory.T
