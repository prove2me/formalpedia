-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedMultiscalePhase_EPR_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/a474e038-d1c1-47cb-9179-20a1bf4e628d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedMultiscalePhase_card

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
    {S B : ℕ} (scale : Fin (S + 1))
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin S → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase (S + 1) B))
        (unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin S → Fin B)) (r, t) := by
  classical
  by_cases selected : p = q
  · subst q
    by_cases residual : r = t
    · subst t
      simp only [ePRState, ↓reduceIte]
      rw [unconditionalSelectedMultiscalePhase_card,
        Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg B), mul_inv]
      exact Complex.ofReal_mul _ _
    · have different :
          unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, r) ≠
            unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, t) := by
          intro equal
          exact residual
            (congrArg Prod.snd
              ((unconditionalSelectedMultiscalePhaseIndexEquiv
                scale).injective equal))
      simp [ePRState, different, residual]
  · have different :
        unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r) ≠
          unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t) := by
        intro equal
        exact selected
          (congrArg Prod.fst
            ((unconditionalSelectedMultiscalePhaseIndexEquiv
              scale).injective equal))
    simp [ePRState, different, selected]
end QuantumParallelRepetition
