-- Prove2me | solution 2 for P2M_GlobalTheory_schurComplement___eq_swap_83d3d265164e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:11.722846+00:00
-- url     : https://prove2.me/submissions/528c797a-8a82-49fb-af41-c7e8a987ea03

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
variable {m n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m]
omit [DecidableEq m] [Fintype m]
namespace GlobalTheory
theorem _root_.solution (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    schurComplement₂₂ G = schurComplement₁₁ (G.submatrix Sum.swap Sum.swap) :=
  rfl
end GlobalTheory
