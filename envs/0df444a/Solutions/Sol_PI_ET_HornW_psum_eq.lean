-- Prove2me | solution 1 for PI.ET.HornW.psum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:16.640328+00:00
-- url     : https://prove2.me/submissions/703e6911-038d-419b-ac29-b5482c0f187e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    psum f k = ∑ i : Fin k, f (Fin.castLE hk i) := by
  unfold psum
  symm
  apply Finset.sum_nbij (fun i : Fin k => Fin.castLE hk i)
  · intro a _
    simp [a.isLt]
  · intro a _ b _ h
    exact Fin.castLE_injective hk h
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb
    exact ⟨⟨b.val, hb⟩, by simp, Fin.ext (by simp)⟩
  · intro a _
    rfl
end PI.ET.HornW
