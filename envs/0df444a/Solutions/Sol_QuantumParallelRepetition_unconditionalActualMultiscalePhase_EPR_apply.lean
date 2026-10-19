-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualMultiscalePhase_EPR_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/2bdc0e08-fe11-411f-95b2-069408f77aec

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedMultiscalePhase_EPR_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {S B : ℕ} (scale : Fin S)
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin (S - 1) → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase S B))
        (unconditionalActualMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalActualMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin (S - 1) → Fin B))
          (r, t) := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhase_EPR_apply
        scale p q r t
end QuantumParallelRepetition
