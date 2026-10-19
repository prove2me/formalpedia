-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485FairSourceClipEnergy_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/3521daa7-09bf-4265-b126-adcb03d51721

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485FairSourceClipEnergy_le

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
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (source_positive : 0 < repeatedPostselectionMass G n S D)
    {w δ : ℝ} {N P L m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (dimension :
      0 < Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (phases : 0 < P) (harmonic : 0 < m)
    (schedule : Fin L → Fin 1)
    (scalar :
      1 / w +
        (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
          w / (N : ℝ) ≤ 3 * δ / 2) :
    unconditionalActualC485FairSourceClipEnergy
        (P := P) (m := m) G n S D width grid fine schedule ≤
      16 * martingaleRate G n S D + 8 * (3 * δ / 2) := by
  exact (unconditionalActualC485FairSourceClipEnergy_le
    (P := P) (m := m)
    G n S D remaining source_positive width grid dimension fine
    phases harmonic schedule).trans (by gcongr)
end QuantumParallelRepetition
