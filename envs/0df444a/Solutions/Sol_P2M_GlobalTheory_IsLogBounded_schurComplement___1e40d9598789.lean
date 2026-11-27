-- Prove2me | solution 1 for P2M_GlobalTheory_IsLogBounded_schurComplement___1e40d9598789
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:43.404636+00:00
-- url     : https://prove2.me/submissions/38583190-0778-49ec-9bfd-2495a7d256bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
open GlobalTheory.IsLogBounded
variable [Fintype m]
namespace GlobalTheory.IsLogBounded
theorem _root_.solution {G : X → Matrix (m ⊕ n) (m ⊕ n) ℂ} (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => schurComplement₂₂ (G x) :=
  (hG.submatrix (e := Sum.swap) (Equiv.sumComm n m).injective).schurComplement₁₁
end GlobalTheory.IsLogBounded
