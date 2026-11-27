-- Prove2me | solution 1 for P2M_GlobalTheory_schurComplement___eq_swap_83d3d265164e
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:17.262827+00:00
-- url     : https://prove2.me/submissions/5c5fe58e-7857-4c8f-96e4-977bc2df75d2

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
theorem _root_.solution (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    schurComplement₂₂ G = schurComplement₁₁ (G.submatrix Sum.swap Sum.swap) := by
  first | rfl | (unfold GlobalTheory.schurComplement₂₂ GlobalTheory.schurComplement₁₁; rfl) | (ext i j; simp [GlobalTheory.schurComplement₂₂, GlobalTheory.schurComplement₁₁])



