-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceSupportedBorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/0f13ad7d-1272-4a4a-819b-74da7eb4b02f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceTuplePsi_norm
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceBaseSupportedBorn
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceOuterBorn_of_base

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (j : Fin L) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m)
        j h.2.1 h.2.2.1)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j‖ ^ 2 *
        exactSourceConditionalWinningProbability G n S D h := by
  classical
  exact
    unconditionalActualFairSourceOuterBorn_of_base
      G n S D a₀ b₀ phases grid harmonic width schedule
      (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
      (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
      (exactSourceTuplePsi G n S D h)
      (exactSourceTuplePsi_norm G n S D h)
      j h.2.1 h.2.2.1
      (exactSourceConditionalWinningProbability G n S D h)
      (unconditionalActualFairSourceBaseSupportedBorn
        G n S D positive a₀ b₀ h supported)
end QuantumParallelRepetition
